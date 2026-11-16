"""Check bilingual formulas and artifact bindings, then render every PDF page."""
from pathlib import Path
import json,hashlib,re,math
import pymupdf as fitz
from PIL import Image,ImageDraw

root=Path(__file__).resolve().parents[1]
base=root/'preprints/LATINON'
audit=base/'02_validation/v1.0'
render=audit/'rendered'
render.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
normalize=lambda s:re.sub(r'\s+','',s)
parity=[]
for folder,stem in [('01_manuscript','latinon'),('05_formalization','formal_companion')]:
    en=(base/folder/f'{stem}_en.md').read_text(encoding='utf-8')
    es=(base/folder/f'{stem}_es.md').read_text(encoding='utf-8')
    displays=lambda s:[normalize(x) for x in re.findall(r'\$\$(.*?)\$\$',s,re.S)]
    inline=lambda s:[normalize(x) for x in re.findall(r'(?<!\$)\$(?!\$)([^$]+?)(?<!\$)\$(?!\$)',re.sub(r'\$\$.*?\$\$','',s,flags=re.S))]
    code=lambda s:re.findall(r'`([^`]+)`',s)
    assert displays(en)==displays(es),(stem,'display parity')
    assert inline(en)==inline(es),(stem,'inline parity')
    assert code(en)==code(es),(stem,'formal identifier parity')
    assert len(re.findall(r'^## ',en,re.M))==len(re.findall(r'^## ',es,re.M))
    assert re.findall(r'https?://[^)\s]+',en)==re.findall(r'https?://[^)\s]+',es)
    parity.append({'pair':stem,'status':'PASS','display_formulas':len(displays(en)),
        'inline_formulas':len(inline(en)),'formal_identifiers':len(code(en))})

typed=json.loads((audit/'TYPESETTING.json').read_text())
documents=[]
for record in typed['documents']:
    for kind in ['source','tex','pdf']:
        assert sha(root/record[kind])==record[kind+'_sha256'],record[kind]
    for log in record['passes']:
        assert sha(root/log['path'])==log['sha256'] and log['exit_code']==0
    source=root/record['source'];tex=root/record['tex'];pdf=root/record['pdf']
    assert sha(root/record['final_log'])==record['final_log_sha256']
    full_log=(root/record['final_log']).read_text(encoding='utf-8',errors='replace')
    assert not re.search(r'Overfull \\hbox|Missing character|^! ',full_log,re.M),pdf.name
    doc=fitz.open(pdf)
    if pdf.stem.startswith('formal_companion_'):
        full_text=re.sub(r'\s+',' ',' '.join(page.get_text() for page in doc))
        for command in ['lake build LatinonFormalization','lake env lean ReviewAxioms.lean','ENNReal.ofReal t']:
            assert command in full_text,(pdf.name,'rendered command mismatch',command)
    pages=[];links=set();sheets=[]
    for index,page in enumerate(doc):
        text=page.get_text()
        assert '\ufffd' not in text,(pdf.name,index+1,'replacement glyph')
        assert len(text.strip())>80,(pdf.name,index+1,'nearly blank')
        for b in page.get_text('blocks'):
            x0,y0,x1,y1=b[:4]
            assert x0>=48 and x1<=page.rect.width-45,(pdf.name,index+1,'horizontal overflow',b[:4])
            assert y0>=35 and y1<=page.rect.height-27,(pdf.name,index+1,'vertical overflow',b[:4])
        for link in page.get_links():
            uri=link.get('uri')
            if uri:
                assert uri.startswith(('https://','mailto:')),uri
                links.add(uri)
        png=render/f'{pdf.stem}_{index+1:02}.png'
        page.get_pixmap(matrix=fitz.Matrix(1.45,1.45),alpha=False).save(png)
        pages.append({'page':index+1,'image':png.relative_to(root).as_posix(),'sha256':sha(png)})
    for offset in range(0,len(pages),2):
        images=[Image.open(root/p['image']).convert('RGB') for p in pages[offset:offset+2]]
        width=max(im.width for im in images)
        height=max(im.height for im in images)
        sheet=Image.new('RGB',(2*width+30,height+45),'#dadada')
        draw=ImageDraw.Draw(sheet)
        for j,im in enumerate(images):
            sheet.paste(im,(10+j*(width+10),35))
            draw.text((14+j*(width+10),10),f'{pdf.stem} — page {offset+j+1}',fill='black')
        path=render/f'{pdf.stem}_pair{offset//2+1:02}.jpg'
        sheet.save(path,quality=92)
        sheets.append(path.relative_to(root).as_posix())
    assert 'https://orcid.org/0009-0003-6068-4096' in links,pdf.name
    if pdf.stem.startswith('latinon_'):
        expected=set(re.findall(r'\]\((https?://[^)\s]+)\)',source.read_text(encoding='utf-8')))
        assert expected<=links,(pdf.name,expected-links)
    documents.append({'pdf':record['pdf'],'pdf_sha256':sha(pdf),'page_count':len(doc),
        'pages':pages,'sheets':sheets,'uris':sorted(links)})
report={'status':'PASS_STATIC_RENDERED_AWAITING_VISUAL','parity':parity,
    'source_tex_pdf_binding':'PASS','all_page_static_geometry':'PASS','pdf_uri_annotations':'PASS','documents':documents}
(audit/'DOCUMENT_AUDIT.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':report['status'],'parity':parity,
  'pages':{Path(x['pdf']).name:x['page_count'] for x in documents}},indent=2))
