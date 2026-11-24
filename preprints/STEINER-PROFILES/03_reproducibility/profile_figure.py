"""Two colors, q=4 and limiting proportions (1/2,1/2)."""
from fractions import Fraction as F
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

def profile(x, y):
    return (x, F(1,2)-3*x-y, 3*(x+y), F(1,2)-x-3*y, y)

vertices = [(0,0),(F(1,6),0),(F(1,8),F(1,8)),(0,F(1,6))]
for v in vertices:
    q = profile(*v)
    assert min(q) >= 0 and sum(q) == 1
    assert sum(i*t for i,t in enumerate(q)) == 2
    assert sum(i*(i-1)*t/2 for i,t in enumerate(q)) == F(3,2)
assert profile(F(1,16),F(1,16)) == tuple(F(i,16) for i in (1,4,6,4,1))
img = Image.new('RGB',(970,615),'white')
d = ImageDraw.Draw(img)
def point(x,y): return (round(240+2670*x),round(510-2670*y))
def font(size):
    for name in ['cambria.ttc','DejaVuSerif.ttf']:
        try: return ImageFont.truetype(name,size)
        except OSError: pass
    return ImageFont.load_default(size=size)
def label(x,y,text,size=26,anchor='mm'):
    d.text((x,y),text,font=font(size),fill='#142729',anchor=anchor)
corners=[point(*v) for v in vertices]
d.polygon(corners,fill='#e5eeed')
d.line(corners+[corners[0]],fill='#28595b',width=4)
d.line([point(0,.18),point(0,0),point(.18,0)],fill='#253238',width=3)
for a,txt in [(0,'0'),(1/16,'1/16'),(1/8,'1/8'),(1/6,'1/6')]:
    x,y=point(a,0); d.line((x,y,x,y+6),fill='black',width=2); label(x,y+23,txt,22)
    x,y=point(0,a); d.line((x-6,y,x,y),fill='black',width=2)
    if a: label(x-13,y,txt,22,'rm')
label(770,510,'x = Q₀',28,'lm');label(236,20,'y = Q₄',28)
d.line([point(0,0),point(1/16,1/16)],fill='#85482b',width=4)
for a,txt in [(0,'Q'),(1/32,'Q½'),(1/16,'P')]:
    x,y=point(a,a);d.ellipse((x-6,y-6,x+6,y+6),fill='#743d27');label(x+14,y-8,txt,26,'lm')
folder=Path(__file__).resolve().parents[1]/'01_manuscript/figures'
folder.mkdir(exist_ok=True)
img.save(folder/'profile_slice.png',dpi=(230,230))
