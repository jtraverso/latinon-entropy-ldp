"""Reproduce the paper and companion in the Paper II series layout."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('file', type=Path)
args = parser.parse_args()
src = args.file.resolve()
root = Path(__file__).resolve().parent
lang = src.stem[-2:]
companion = 'companion' in src.name
data = src.read_text(encoding='utf-8').strip()
title = data.splitlines()[0][2:]
body = data[data.index('\n## ')+1:]
cache = Path.home()/'.cache/nw-typesetting'
pandoc = shutil.which('pandoc') or str(cache/'pandoc/pandoc-3.12.1/pandoc.exe')
tectonic = str(cache/'tectonic/tectonic.exe') if (cache/'tectonic/tectonic.exe').exists() else 'tectonic'
layout = (root/'layout'/f'series_{lang}.tex').read_text(encoding='utf-8')
texbody = subprocess.run([pandoc,'--from=markdown+tex_math_single_backslash','--to=latex','--wrap=none'],input=body,text=True,encoding='utf-8',capture_output=True,check=True).stdout
texbody = re.sub(r'\\texttt\{([a-zA-Z0-9_\\.]+)\}',lambda a:r'\path{'+a[1].replace(r'\_','_')+'}',texbody)
texbody = re.sub(r'\\begin\{longtable\}\[\]\{@\{\}lll@\{\}\}',lambda _:r'\begin{longtable}[]{@{}p{.18\linewidth}p{.44\linewidth}p{.29\linewidth}@{}}',texbody)
texbody = texbody.replace(r'\textbf{Theorem 1.1.}',r'\Needspace{7\baselineskip}\textbf{Theorem 1.1.}').replace(r'\textbf{Corollary 10.1.}',r'\Needspace{7\baselineskip}\textbf{Corollary 10.1.}')
layout+=r'''
\clubpenalty=10000\widowpenalty=10000\displaywidowpenalty=10000
\usepackage{tikz}
\AtBeginEnvironment{longtable}{\Needspace{16\baselineskip}}
'''
meta=r'\hypersetup{pdftitle={'+title+r'},pdfauthor={Juan Pablo Traverso Gianini},pdflang={'+lang+r'},colorlinks=true,linkcolor=blue,urlcolor=blue,citecolor=blue}'+'\n'
meta+=r'\title{'+title+r'}'+'\n'+r'\author{Juan Pablo Traverso Gianini\\\small '+('Independent researcher, Santiago, Chile' if lang=='en' else 'Investigador independiente, Santiago, Chile')+r'\\\small \href{mailto:jtraverso@gmail.com}{jtraverso@gmail.com}\\\small \href{https://orcid.org/0009-0003-6068-4096}{ORCID: 0009-0003-6068-4096}}'
meta+=r'\date{}\begin{document}\raggedbottom\maketitle'+'\n'+r'\begin{center}'+'\n'
meta+=r'\textbf{'+('Paper III. Combinatorial entropy and counting.' if lang=='en' else 'Paper III. Entropía combinatoria y conteo.')+r'}\\'+'\n'
meta+=r'\textbf{'+('Preprint 1.0 --- November 24, 2026.' if lang=='en' else 'Preprint 1.0 --- 24 de noviembre de 2026.')+r'}\\'+'\n'
meta+='DOI'+r': \url{https://doi.org/10.5281/zenodo.24501236}.\\'+'\n'
meta+=r'\href{https://github.com/jtraverso/latinon-entropy-ldp/tree/main/preprints/STEINER-PROFILES/05_formalization/lean}{'+('Lean sources in the series repository' if lang=='en' else 'Fuentes Lean en el repositorio de la serie')+r'}\end{center}'+'\n'
if not companion:
    # Keep the example, picture and bilingual caption together at the point of use.
    def example_figure(match):
        label = 'Figure 1.' if lang == 'en' else 'Figura 1.'
        return (r'\begin{center}\begin{minipage}{.82\linewidth}\centering'+'\n'
                +match[1]+'\n'+r'\par\smallskip\small\textbf{'+label+'} '
                +match[2]+'\n'+r'\end{minipage}\end{center}')
    texbody, count = re.subn(r'\\begin\{figure\}\s*\\centering\s*(\\includegraphics[^\n]+)\s*\\caption\{([^\n]+)\}\s*\\end\{figure\}', example_figure, texbody)
    assert count == 1, 'Expected the two-color profile figure'
for label in ['references','referencias']:
    marker=r'\label{'+label+'}'
    texbody=texbody.replace(marker,marker+'\n'+r'\raggedright')
tex=src.with_suffix('.tex')
tex.write_text(layout+meta+texbody+'\n\\end{document}\n',encoding='utf-8')
env=os.environ.copy()
subprocess.run([tectonic,'--only-cached','--keep-logs',tex.name],cwd=src.parent,env=env,check=True)
