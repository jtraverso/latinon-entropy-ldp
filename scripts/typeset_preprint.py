"""Convert semantic Markdown bodies through the frozen CDR layout; serial PDFs."""
from pathlib import Path
import subprocess,json,hashlib,os,re,shutil

root=Path(__file__).resolve().parents[1]
base=root/'preprints/LATINON'
logs=base/'02_validation/v1.0/typesetting'
logs.mkdir(parents=True,exist_ok=True)
cache=Path(os.environ.get('LOCALAPPDATA',str(Path.home()/'AppData/Local')))
pandoc=shutil.which('pandoc') or str(Path.home()/'.cache/nw-typesetting/pandoc/pandoc-3.12.1/pandoc.exe')
tectonic=shutil.which('tectonic') or str(Path.home()/'.cache/nw-typesetting/tectonic/tectonic.exe')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
fontenv=os.environ.copy()
fontconfig=root/'tmp/fontconfig.xml'
fontconfig.parent.mkdir(exist_ok=True)
fontconfig.write_text('<?xml version="1.0"?>\n<fontconfig><dir>C:/Windows/Fonts</dir><cachedir>'+str(root/'tmp/fontcache').replace('\\','/')+'</cachedir></fontconfig>\n',encoding='utf-8')
fontenv['FONTCONFIG_FILE']=str(fontconfig)
for folder,stem in [('01_manuscript','latinon'),('05_formalization','formal_companion')]:
    for lang in ['en','es']:
        source=base/folder/f'{stem}_{lang}.md'
        md=source.read_text(encoding='utf-8')
        title=md.splitlines()[0].removeprefix('# ')
        body=md[md.index('## '):]
        conv=subprocess.run([pandoc,'--from=markdown+tex_math_dollars','--to=latex','--wrap=none'],
          input=body,text=True,encoding='utf-8',capture_output=True,check=True)
        texbody=conv.stdout
        # Long formal identifiers are breakable paths, not overflowing typewriter boxes.
        def inline_code(match):
            value=match.group(1)
            if ' ' in value:return r'\texttt{'+value+'}'
            return r'\path{'+value.replace(r'\_','_')+'}'
        texbody=re.sub(r'\\texttt\{([^{}]+)\}',inline_code,texbody)
        texbody=re.sub(r'\\textbf\{((?:Theorem|Lemma|Corollary|Proposition|Teorema|Lema|Corolario|Proposición) [^{}]+)\}',lambda m:r'\Needspace{7\baselineskip}\textbf{'+m.group(1)+'}',texbody)
        texbody=re.sub(r'\\textbf\{(\d+\. [^{}]+)\}',lambda m:r'\Needspace{6\baselineskip}\textbf{'+m.group(1)+'}',texbody)
        texbody=texbody.replace('\n\\[','\n\\nopagebreak[4]\n\\[')
        preamble=(base/f'03_reproducibility/layout/series_{lang}.tex').read_text(encoding='utf-8')
        # Names in (9.1) are language-independent mathematical notation.
        preamble += '\n'+r'\newcommand{\KL}{\operatorname{KL}}'+'\n'
        preamble += r'\clubpenalty=10000\widowpenalty=10000\displaywidowpenalty=10000'+'\n'
        meta=(r'\hypersetup{pdftitle={'+title+r'},pdfauthor={Juan Pablo Traverso Gianini},pdflang={'+lang+r'},colorlinks=true,linkcolor=blue,urlcolor=blue,citecolor=blue}'+'\n'+
          r'\title{'+title+'}\n'+
          r'\author{Juan Pablo Traverso Gianini\\\small Independent researcher, Santiago, Chile\\\small \href{mailto:jtraverso@gmail.com}{jtraverso@gmail.com}\\\small \href{https://orcid.org/0009-0003-6068-4096}{ORCID: 0009-0003-6068-4096}}'+'\n'+
          r'\date{}\begin{document}\raggedbottom\maketitle'+'\n'+
          (r'\textbf{Preprint 1.0 --- 16 November 2026.}' if lang=='en' else r'\textbf{Preprint 1.0 --- 16 de noviembre de 2026.}')+'\n\n'+r'\textbf{'+('Repository' if lang=='en' else 'Repositorio')+r':} \url{https://github.com/jtraverso/latinon-entropy-ldp}.'+'\n\n')
        tex=source.with_suffix('.tex')
        tex.write_text(preamble+meta+texbody+'\n\\end{document}\n',encoding='utf-8')
        passes=[]
        for attempt in [1,2]:
            command=[tectonic,'--keep-logs','--keep-intermediates',tex.name]
            run=subprocess.run(command,cwd=tex.parent,capture_output=True,text=True,encoding='utf-8',errors='replace',env=fontenv)
            log=logs/f'{tex.stem}_pass{attempt}.log'
            log.write_text(run.stdout+'\n'+run.stderr,encoding='utf-8')
            assert run.returncode==0,log
            passes.append({'path':log.relative_to(root).as_posix(),'sha256':sha(log),'exit_code':run.returncode})
        pdf=tex.with_suffix('.pdf');assert pdf.is_file()
        final_log=logs/f'{tex.stem}.log'
        shutil.move(str(tex.with_suffix('.log')),final_log)
        records.append({'source':source.relative_to(root).as_posix(),'source_sha256':sha(source),
          'tex':tex.relative_to(root).as_posix(),'tex_sha256':sha(tex),
          'pdf':pdf.relative_to(root).as_posix(),'pdf_sha256':sha(pdf),'passes':passes,
          'final_log':final_log.relative_to(root).as_posix(),'final_log_sha256':sha(final_log)})
        print('Built '+pdf.name,flush=True)
(base/'02_validation/v1.0/TYPESETTING.json').write_text(json.dumps({'status':'PASS_COMPILATION','documents':records},indent=2)+'\n',encoding='utf-8')
