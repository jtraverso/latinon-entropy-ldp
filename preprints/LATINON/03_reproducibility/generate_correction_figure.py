"""Generate the bilingual vector schematic of the proved correction argument."""
from pathlib import Path
import hashlib,json,os,subprocess,datetime
import pymupdf

root=Path(__file__).resolve().parents[3]
folder=root/'preprints/LATINON/01_manuscript/figures'
folder.mkdir(exist_ok=True)
tectonic=Path.home()/'.cache/nw-typesetting/tectonic/tectonic.exe'
env=os.environ.copy();env['FONTCONFIG_FILE']=str(root/'tmp/fontconfig.xml')
records=[]
for lang,head,left,right,shift in [
    ('en','Residual paths','Same side: at most four edges','Potential centering','Subtract the midpoint'),
    ('es','Caminos residuales','Mismo lado: a lo sumo cuatro aristas','Centrado del potencial','Restar el punto medio')]:
    source=folder/f'correction_paths_{lang}.tex'
    text=r'''\documentclass[10pt]{article}
\usepackage[paperwidth=16cm,paperheight=5.5cm,margin=0.1cm]{geometry}
\usepackage{fontspec}
\setmainfont{lmroman10-regular.otf}[BoldFont=lmroman10-bold.otf]
\usepackage{amsmath,amssymb,tikz}
\usetikzlibrary{arrows.meta,decorations.pathreplacing}
\pagestyle{empty}\setlength{\parindent}{0pt}
\begin{document}
\begin{tikzpicture}[x=1cm,y=1cm,>=Stealth,vertex/.style={circle,draw,fill=white,inner sep=2pt}]
\useasboundingbox (-0.5,-1.4) rectangle (15.1,3.6);
\node[font=\bfseries] at (3.4,3.2) {HEAD};
\node[vertex] (a) at (0,2.2) {$y_0$};
\node[vertex] (b) at (1.25,0.7) {$z_1$};
\node[vertex] (c) at (2.5,2.2) {$y_1$};
\node[vertex] (d) at (3.75,0.7) {$z_2$};
\node[vertex] (e) at (5,2.2) {$y_2$};
\node[vertex] (f) at (6.25,0.7) {$z$};
\draw[->,thick,blue!55!black] (a)--(b);
\draw[->,thick,blue!55!black] (b)--(c);
\draw[->,thick,blue!55!black] (c)--(d);
\draw[->,thick,blue!55!black] (d)--(e);
\draw[->,thick,dashed] (e)--(f) node[midway,right] {$+1$};
\draw[decorate,decoration={brace,amplitude=4pt}] (0,2.7)--(5,2.7);
\node[align=center] at (2.5,0) {LEFT};
\node at (3.2,-0.7) {$\operatorname{diam}\le 5$};
\draw[gray!60] (7.2,-0.9)--(7.2,3.5);
\node[font=\bfseries] at (11.2,3.2) {RIGHT};
\draw[thick] (8.2,2.2)--(14.2,2.2);
\draw (8.2,2.05)--(8.2,2.35) node[above] {$\min\pi$};
\draw (14.2,2.05)--(14.2,2.35) node[above] {$\max\pi$};
\node[fill=white] at (11.2,2.2) {$\max\pi-\min\pi\le 5$};
\draw[->] (11.2,1.85)--(11.2,0.9) node[midway,right,font=\small] {SHIFT};
\draw[thick] (8.2,0.5)--(14.2,0.5);
\draw (8.2,0.35)--(8.2,0.65) node[below=6pt] {$-5/2$};
\draw (14.2,0.35)--(14.2,0.65) node[below=6pt] {$5/2$};
\node[fill=white] at (11.2,0.5) {$|u_y|,|v_z|\le 5/2$};
\node at (11.2,-0.7) {$\|Q-M\|_1\le (5/2)D(M)$};
\end{tikzpicture}
\end{document}
'''
    for key,value in [('HEAD',head),('LEFT',left),('RIGHT',right),('SHIFT',shift)]:text=text.replace(key,value)
    source.write_text(text,encoding='utf-8')
    p=subprocess.run([str(tectonic),'--keep-logs',source.name],cwd=folder,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
    (root/f'tmp/correction_figure_{lang}.log').write_text(p.stdout+'\n'+p.stderr,encoding='utf-8')
    assert p.returncode==0,p.stderr
    pdf=source.with_suffix('.pdf');png=source.with_suffix('.png')
    doc=pymupdf.open(pdf);assert len(doc)==1
    doc[0].get_pixmap(matrix=pymupdf.Matrix(2.0,2.0),alpha=False).save(png)
    source.with_suffix('.log').unlink(missing_ok=True)
    records.append({suffix:{'path':source.with_suffix(suffix).relative_to(root).as_posix(),
        'sha256':hashlib.sha256(source.with_suffix(suffix).read_bytes()).hexdigest()} for suffix in ['.tex','.pdf','.png']})
record={'status':'GENERATED_AWAITING_VISUAL_REVIEW','generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'scope':'Schematic of the existing proved residual diameter and centered potential bounds; no new claim of optimality',
    'documents':records,'generated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(root/'preprints/LATINON/02_validation/v1.0/CORRECTION_FIGURE.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('Generated bilingual correction schematic')
