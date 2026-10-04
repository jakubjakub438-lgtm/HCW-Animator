import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import xml.etree.ElementTree as ET
import math, os, base64, io, tempfile, shutil, subprocess, threading
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont, ImageTk
import imageio_ffmpeg

APP_TITLE = "HCW Animator v0.1"
FPS = 24
DEFAULT_MOVE = 1.5
DEFAULT_HOLD = 1.0

def txt(e,k,d=""):
    q=e.find(k) if e is not None else None
    return q.text if q is not None and q.text is not None else d
def flt(e,k,d=0.0):
    try: return float(txt(e,k,str(d)))
    except: return d
def evs(e):
    q=e.find("ObjectEvents")
    return q.findall("OnOffEvent") if q is not None else []
def first_true(e, default=999999):
    a=[int(txt(x,"sequence","0")) for x in evs(e) if txt(x,"active").lower()=="true"]
    return min(a) if a else default
def active_at(e,seq):
    arr=sorted(evs(e), key=lambda z:int(txt(z,"sequence","0")))
    state=None
    for z in arr:
        if int(txt(z,"sequence","0"))<=seq:
            state=txt(z,"active").lower()=="true"
    return bool(state)
def active_rot(e,tag,seq):
    rs=e.findall("./SubObjects/"+tag)
    if not rs: return 0.0
    disabled=set()
    for z in sorted(evs(e),key=lambda q:int(txt(q,"sequence","0"))):
        if int(txt(z,"sequence","0"))<=seq:
            disabled={s.strip() for s in txt(z,"disabledRotators").split(",") if s.strip()}
    enabled=[r for r in rs if txt(r,"uniqueID") not in disabled]
    r=enabled[0] if enabled else rs[0]
    return flt(r,"angle")
def shortest(a,b):
    return a+((b-a+math.pi)%(2*math.pi)-math.pi)
def lerp(a,b,t): return a+(b-a)*t

class HCWScene:
    def __init__(self, path):
        self.path=Path(path)
        self.root=ET.parse(path).getroot()
        self.canvas=self.root.find("./CurrentSnapshot/Canvas")
        if self.canvas is None: raise ValueError("HCW: chýba CurrentSnapshot/Canvas.")
        bg=self.canvas.find("Background")
        if bg is None: raise ValueError("HCW: chýba Background.")
        picid=txt(bg,"pictureUniqueID")
        pics=self.root.findall("./Pictures/Picture")
        pic=next((p for p in pics if txt(p,"uniqueID")==picid),None)
        if pic is None or not txt(pic,"base64Data"):
            raise ValueError("HCW: nenašiel sa vložený podkladový obrázok.")
        self.base=Image.open(io.BytesIO(base64.b64decode(txt(pic,"base64Data")))).convert("RGB")
        self.W,self.H=self.base.size

        # Exact transform used by the two validated scenes TEST04 and TEST05.
        # HCW Background objectScaleX supplies the per-scene scale.
        bgscale=flt(bg,"objectScaleX")
        if bgscale<=0: raise ValueError("HCW: neplatný Background objectScaleX.")
        self.ppu=.829*.607753125/bgscale
        self.ox=self.W/2 + self.ppu*flt(bg,"x")
        self.oy=self.H/2 + self.ppu*flt(bg,"y")

        self.chars=self.canvas.findall("Character")
        self.charid={txt(e,"uniqueID"):e for e in self.chars}
        color_name={}
        for cap in self.canvas.findall("Caption"):
            uid=txt(cap,"attachObjectID"); name=txt(cap,"userText").strip()
            if uid in self.charid and name:
                color_name[txt(self.charid[uid],"colorName")]=name

        animchars=[e for e in self.chars if evs(e)]
        aid={txt(e,"uniqueID"):e for e in animchars}
        walks=self.canvas.findall("WalkArrow")
        adj={u:set() for u in aid}
        for w in walks:
            a,b=txt(w,"fromConstraints"),txt(w,"toConstraints")
            if a in adj and b in adj:
                adj[a].add(b); adj[b].add(a)
        comps=[]; seen=set()
        for u in aid:
            if u in seen: continue
            st=[u]; seen.add(u); comp=[]
            while st:
                v=st.pop(); comp.append(v)
                for n in adj[v]:
                    if n not in seen: seen.add(n); st.append(n)
            comps.append(comp)
        self.actors=[]
        for comp in comps:
            es=[aid[u] for u in comp]
            color=txt(es[0],"colorName")
            name=color_name.get(color,color or "ACTOR")
            aw=[w for w in walks if txt(w,"fromConstraints") in comp and txt(w,"toConstraints") in comp]
            self.actors.append((name,color,es,aw))

        self.cams=self.canvas.findall("Camera")
        self.cid={txt(c,"uniqueID"):c for c in self.cams}
        self.tracks=self.canvas.findall("Track")
        self.dollies=[]; dolly_members=set()
        for tr in self.tracks:
            tid=txt(tr,"uniqueID")
            members={txt(tr,"fromConstraints"),txt(tr,"toConstraints")}
            members |= {txt(c,"uniqueID") for c in self.cams if txt(c,"snapPath")==tid}
            members={u for u in members if u in self.cid}
            if members:
                dolly_members |= members
                self.dollies.append((tr,sorted([self.cid[u] for u in members],key=first_true)))
        self.statics=[c for c in self.cams if txt(c,"uniqueID") not in dolly_members]

        seqs=sorted({int(txt(x,"sequence","0")) for x in self.root.findall(".//TimeNumber")})
        if not seqs:
            seqs=sorted({int(txt(x,"sequence","0")) for e in animchars+self.cams for x in evs(e)})
        self.seqs=seqs
        self.maxseq=max(seqs) if seqs else 0
        self.aid=aid

    def P(self,x,y): return (self.ox+self.ppu*x, self.oy+self.ppu*y)

    def object_path(self,w):
        a=self.aid[txt(w,"fromConstraints")]; b=self.aid[txt(w,"toConstraints")]
        pts=[(flt(a,"x"),flt(a,"y"))]
        pe=w.find("Points")
        if pe is not None: pts += [(flt(p,"x"),flt(p,"y")) for p in pe.findall("Point")]
        pts += [(flt(b,"x"),flt(b,"y"))]
        return pts

    @staticmethod
    def along(pts,t):
        if not pts: raise ValueError("Prázdna HCW dráha.")
        ds=[0.0]
        for i in range(1,len(pts)):
            ds.append(ds[-1]+math.hypot(pts[i][0]-pts[i-1][0],pts[i][1]-pts[i-1][1]))
        if ds[-1]<=0: return pts[-1]
        d=max(0,min(1,t))*ds[-1]
        for i in range(1,len(ds)):
            if d<=ds[i]:
                q=(d-ds[i-1])/(ds[i]-ds[i-1] or 1)
                return lerp(pts[i-1][0],pts[i][0],q),lerp(pts[i-1][1],pts[i][1],q)
        return pts[-1]

    def track_path(self,tr):
        a=self.cid.get(txt(tr,"fromConstraints")); b=self.cid.get(txt(tr,"toConstraints"))
        if a is None or b is None: raise ValueError("HCW Track nemá platné koncové kamery.")
        pts=[(flt(a,"x"),flt(a,"y"))]
        pe=tr.find("Points")
        if pe is not None:
            raw=[(flt(p,"x"),flt(p,"y")) for p in pe.findall("Point")]
            # avoid duplicated endpoints only
            for p in raw:
                if math.hypot(p[0]-pts[-1][0],p[1]-pts[-1][1])>1e-9: pts.append(p)
        bp=(flt(b,"x"),flt(b,"y"))
        if math.hypot(bp[0]-pts[-1][0],bp[1]-pts[-1][1])>1e-9: pts.append(bp)
        return pts

    def camera_track_fraction(self,c,tr):
        tid=txt(tr,"uniqueID")
        if txt(c,"uniqueID")==txt(tr,"fromConstraints"): return 0.0
        if txt(c,"uniqueID")==txt(tr,"toConstraints"): return 1.0
        if txt(c,"snapPath")==tid:
            # snapPercent is the HCW-recorded position on the Track.
            return flt(c,"snapPercent")
        raise ValueError("Kamera patrí Dolly, ale nemá preukázanú pozíciu na Tracku.")

    def summary(self):
        return (f"Postavy: {len(self.actors)} | "
                f"Dolly: {len(self.dollies)} | Statické kamery: {len(self.statics)} | "
                f"Animačné sekvencie: {len(self.seqs)}")

COL={"Yellow":(255,235,0),"Cyan":(80,235,215),"Pink":(220,110,220),
     "Blue":(70,175,255),"Red":(245,80,80),"Green":(70,210,100)}

def get_fonts():
    for p in [r"C:\Windows\Fonts\arialbd.ttf", r"C:\Windows\Fonts\arial.ttf"]:
        if os.path.exists(p):
            try:
                return ImageFont.truetype(p,16),ImageFont.truetype(p,13)
            except: pass
    return ImageFont.load_default(),ImageFont.load_default()

FONT,SMALL=get_fonts()

def camicon(d,cx,cy,ang,label,col=(230,60,200)):
    ca,sa=math.cos(ang),math.sin(ang)
    def tr(x,y): return (cx+x*ca-y*sa,cy+x*sa+y*ca)
    d.polygon([tr(-11,-8),tr(9,-8),tr(9,8),tr(-11,8)],fill=col,outline="black")
    for x in (-5,5):
        q=tr(x,-13); d.ellipse((q[0]-5,q[1]-5,q[0]+5,q[1]+5),fill=col,outline="black",width=2)
    d.polygon([tr(9,-5),tr(20,-9),tr(20,9),tr(9,5)],fill=col,outline="black")
    d.text((cx+14,cy-22),label,fill="black",font=SMALL)

def frame(scene, seq, moving=False, u=0.0):
    im=scene.base.copy(); d=ImageDraw.Draw(im)
    for name,color,es,aws in scene.actors:
        e0=next((e for e in es if active_at(e,seq)),None)
        if e0 is None: continue
        x,y=flt(e0,"x"),flt(e0,"y"); a0=active_rot(e0,"RotatorCharacter",seq); ang=a0
        if moving:
            e1=next((e for e in es if active_at(e,seq+1)),None)
            if e1 is not None:
                if txt(e1,"uniqueID")!=txt(e0,"uniqueID"):
                    w=next((w for w in aws if txt(w,"fromConstraints")==txt(e0,"uniqueID") and txt(w,"toConstraints")==txt(e1,"uniqueID")),None)
                    if w is None:
                        raise ValueError(f"{name}: HCW mení pozíciu medzi sekvenciami {seq+1} a {seq+2}, ale nenašiel sa príslušný WalkArrow. Export zastavený.")
                    x,y=scene.along(scene.object_path(w),u)
                a1=active_rot(e1,"RotatorCharacter",seq+1)
                ang=lerp(a0,shortest(a0,a1),u)
        cx,cy=scene.P(x,y); col=COL.get(color,(200,200,200))
        d.ellipse((cx-16,cy-16,cx+16,cy+16),fill=col,outline="black",width=3)
        d.line((cx,cy,cx+14*math.cos(ang),cy+14*math.sin(ang)),fill="black",width=3)
        d.text((cx-18,cy-33),name,fill="black",font=SMALL)

    for di,(tr,dcams) in enumerate(scene.dollies,1):
        c0=next((c for c in dcams if first_true(c)==seq),None)
        if c0 is None:
            prev=[c for c in dcams if first_true(c)<=seq]
            c0=prev[-1] if prev else None
        if c0:
            x,y=flt(c0,"x"),flt(c0,"y"); a0=active_rot(c0,"RotatorCamera",seq); ang=a0
            if moving:
                c1=next((c for c in dcams if first_true(c)==seq+1),None)
                if c1:
                    p0=scene.camera_track_fraction(c0,tr); p1=scene.camera_track_fraction(c1,tr)
                    x,y=scene.along(scene.track_path(tr),lerp(p0,p1,u))
                    a1=active_rot(c1,"RotatorCamera",seq+1)
                    ang=lerp(a0,shortest(a0,a1),u)
            camicon(d,*scene.P(x,y),ang,f"DOLLY {di}")

    for si,c in enumerate(scene.statics,1):
        if active_at(c,seq):
            ang=active_rot(c,"RotatorCamera",seq)
            if moving and active_at(c,seq+1):
                a1=active_rot(c,"RotatorCamera",seq+1)
                ang=lerp(ang,shortest(ang,a1),u)
            camicon(d,*scene.P(flt(c,"x"),flt(c,"y")),ang,f"CAM {si}")
    return im

def render(scene,out_path,move_s,hold_s,progress=None):
    temp=Path(tempfile.mkdtemp(prefix="hcw_anim_"))
    try:
        total=(scene.maxseq+1)*hold_s + scene.maxseq*move_s
        n=max(1,int(round(total*FPS)))
        for fi in range(n):
            t=fi/FPS; local=t; seq=0; moving=False; u=0.0
            for s in range(scene.maxseq+1):
                if local<hold_s: seq=s; break
                local-=hold_s
                if s<scene.maxseq:
                    if local<move_s:
                        seq=s; moving=True; u=local/move_s if move_s else 1.0; break
                    local-=move_s
            im=frame(scene,seq,moving,u)
            im.save(temp/f"{fi:05d}.jpg",quality=90)
            if progress: progress(int((fi+1)*85/n))
        ffmpeg=imageio_ffmpeg.get_ffmpeg_exe()
        cmd=[ffmpeg,"-y","-framerate",str(FPS),"-i",str(temp/"%05d.jpg"),
             "-c:v","libx264","-pix_fmt","yuv420p","-crf","20","-movflags","+faststart",str(out_path)]
        p=subprocess.run(cmd,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,text=True)
        if p.returncode!=0: raise RuntimeError("FFmpeg export zlyhal:\n"+p.stderr[-1500:])
        if progress: progress(100)
    finally:
        shutil.rmtree(temp,ignore_errors=True)

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE); self.geometry("920x700"); self.minsize(760,560)
        self.scene=None; self.preview_img=None
        top=tk.Frame(self); top.pack(fill="x",padx=12,pady=10)
        tk.Button(top,text="OTVORIŤ HCW",command=self.open_hcw,width=18).pack(side="left")
        tk.Button(top,text="PREHĽAD",command=self.show_preview,width=14).pack(side="left",padx=8)
        tk.Button(top,text="EXPORT MP4",command=self.export_mp4,width=18).pack(side="left")
        opts=tk.Frame(self); opts.pack(fill="x",padx=12)
        tk.Label(opts,text="Pohyb (s):").pack(side="left")
        self.move=tk.StringVar(value=str(DEFAULT_MOVE)); tk.Entry(opts,textvariable=self.move,width=6).pack(side="left",padx=(4,16))
        tk.Label(opts,text="Státie na bode (s):").pack(side="left")
        self.hold=tk.StringVar(value=str(DEFAULT_HOLD)); tk.Entry(opts,textvariable=self.hold,width=6).pack(side="left",padx=4)
        self.status=tk.StringVar(value="Otvorte .hcw súbor.")
        tk.Label(self,textvariable=self.status,anchor="w").pack(fill="x",padx=12,pady=8)
        self.pb=ttk.Progressbar(self,maximum=100); self.pb.pack(fill="x",padx=12)
        self.canvas=tk.Canvas(self,bg="#222"); self.canvas.pack(fill="both",expand=True,padx=12,pady=12)

    def open_hcw(self):
        p=filedialog.askopenfilename(filetypes=[("Shot Designer HCW","*.hcw"),("Všetky súbory","*.*")])
        if not p:return
        try:
            self.scene=HCWScene(p)
            self.status.set(Path(p).name+" | "+self.scene.summary())
            self.show_preview()
        except Exception as e:
            self.scene=None; messagebox.showerror(APP_TITLE,str(e))

    def show_preview(self):
        if not self.scene:return
        try:
            im=frame(self.scene,0,False,0)
            cw=max(100,self.canvas.winfo_width()); ch=max(100,self.canvas.winfo_height())
            im.thumbnail((cw-20,ch-20),Image.LANCZOS)
            self.preview_img=ImageTk.PhotoImage(im)
            self.canvas.delete("all")
            self.canvas.create_image(cw//2,ch//2,image=self.preview_img,anchor="center")
        except Exception as e: messagebox.showerror(APP_TITLE,str(e))

    def export_mp4(self):
        if not self.scene:
            messagebox.showwarning(APP_TITLE,"Najprv otvorte HCW."); return
        try:
            mv=float(self.move.get()); hd=float(self.hold.get())
            if mv<0 or hd<0: raise ValueError
        except:
            messagebox.showerror(APP_TITLE,"Časy musia byť nezáporné čísla."); return
        out=filedialog.asksaveasfilename(defaultextension=".mp4",filetypes=[("MP4 video","*.mp4")])
        if not out:return
        self.pb["value"]=0; self.status.set("Exportujem...")
        def prog(v):
            self.after(0,lambda:self.pb.configure(value=v))
        def job():
            try:
                render(self.scene,out,mv,hd,prog)
                self.after(0,lambda:(self.status.set("Hotovo: "+out),messagebox.showinfo(APP_TITLE,"MP4 export dokončený.")))
            except Exception as e:
                self.after(0,lambda:messagebox.showerror(APP_TITLE,str(e)))
        threading.Thread(target=job,daemon=True).start()

if __name__=="__main__":
    App().mainloop()
