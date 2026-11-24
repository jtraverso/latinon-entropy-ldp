"""Read-only local verification of the exact Paper III edition, including both ZIPs."""
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
P = ROOT/'preprints/STEINER-PROFILES'
F = P/'05_formalization'
V = P/'02_validation'
DOI = '10.5281/zenodo.24501236'
TITLE = 'Counting Steiner designs with prescribed color profiles'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(file):
    return json.loads(file.read_text(encoding='utf-8'))

def checked_archive(path):
    line = path.with_suffix('.zip.sha256').read_text().strip()
    assert line == sha(path.read_bytes())+'  '+path.name, path
    return zipfile.ZipFile(path)

def verify():
    meta = load(V/'ZENODO_RESERVATION.json')
    assert (meta['title'],meta['doi'],meta['version'],meta['language'],meta['submitted']) == (TITLE,DOI,'1.0','eng',False)
    papers = [r for r in load(ROOT/'PUBLICATION_INDEX.json')['papers'] if r['id']=='STEINER-PROFILES']
    assert len(papers)==1 and papers[0]['doi']==DOI and papers[0]['title']==TITLE
    assert DOI in (P/'CITATION.cff').read_text()
    docs=load(V/'TYPESETTING.json')
    assert len(docs)==4
    for doc in docs:
        pdf=P/doc['pdf']
        for path,h in [(pdf,doc['sha256']),(pdf.with_suffix('.tex'),doc['tex_sha256']),(pdf.with_suffix('.md'),doc['source_sha256'])]:
            assert sha(path.read_bytes())==h,path
        assert len(doc['pages_rendered'])==doc['pages']
        for page in doc['pages_rendered']:
            assert sha((P/page['file']).read_bytes())==page['sha256'],page
        tex=pdf.with_suffix('.tex').read_text(encoding='utf-8')
        assert 'Preprint 1.0' in tex and DOI in tex and 'encurso' not in tex
    arg=[]
    for lang in ('en','es'):
        src=(P/f'01_manuscript/steiner_profiles_{lang}.md').read_text(encoding='utf-8')
        assert src.count(r'\square')==5
        assert '$C_q=2(q-2)(q-1)$' in src
        arg.append(re.findall(r'\\\[(.*?)\\\]',src,re.S))
        start,end=('## Acknowledgments','## References') if lang=='en' else ('## Agradecimientos','## Referencias')
        prev=(ROOT/f'preprints/COLORSTATS/01_manuscript/color_stats_{lang}.md').read_text(encoding='utf-8')
        assert src[src.index(start):src.index(end)]==prev[prev.index(start):prev.index(end)].replace('[39]','[5]')
    assert arg[0]==arg[1] and len(arg[0])==load(V/'SEMANTIC_DIFF.json')['bilingual_displays']
    subprocess.run([sys.executable,'-B',str(P/'03_reproducibility/check_examples.py')],check=True)
    with checked_archive(F/'steiner-profiles-lean.zip') as z:
        names=z.namelist()
        assert len(names)==len(set(names)) and z.testzip() is None
        manifest=(F/'SHA256SUMS').read_bytes()
        assert manifest==z.read('SHA256SUMS')
        entries={n:h for h,n in (line.split('  ',1) for line in manifest.decode().splitlines())}
        assert set(entries)==set(names)-{'SHA256SUMS'}
        assert 'verification/PROOFS.txt' in entries
        for n,h in entries.items():
            assert sha(z.read(n))==h,n
            if n!='verification/PROOFS.txt':assert (F/n).read_bytes()==z.read(n),n
        assert z.read('lean/LICENSE')==(ROOT/'LICENSE').read_bytes()
        assert len([n for n in names if n.startswith('lean/') and n.endswith('.lean')])==162
        assert re.search(rb'PASS_KERNEL modules=162 declarations=1997',z.read('verification/kernel.log'))
        assert b'loading 59 external imports' in z.read('verification/kernel.log')
        rows=list(csv.DictReader(io.StringIO(z.read('verification/THEOREMS.tsv').decode()),delimiter='\t'))
        dec={row['declaration'] for row in rows}
        assert len(rows)==1750 and len(dec)==1741
        allowed={'propext','Quot.sound','Classical.choice'}
        assert all(set(row['axioms'].split(', '))-{''}<=allowed for row in rows)
        for end in ['PhysicalCompletion.eventually_designFibre_bilateral','UpperCounting.eventually_card_designFibre_upper_entropy','ProfileLDP.designProfileLDP_probability','SlotPairMargins.round_quotas']:
            assert 'KqR75.'+end in dec and end.encode() in z.read('verification/canonical.log')
        assert b'proofs=1750' in z.read('verification/catalogue.log')
    for receipt in V.glob('*/STATUS.json'):
        for n,h in load(receipt).get('evidence_sha256',{}).items():
            assert sha((receipt.parent/n).read_bytes())==h,n
    report=load(ROOT/'publication/STEINER_PROFILES_RELEASE_AUDIT.json')
    assert report==load(V/'RELEASE_AUDIT.json') and report['status']=='PASS_INTERNAL_RELEASE_AUDIT'
    assert set(report['checks'].values())=={'PASS'}
    for name,digest in report['records'].items():
        assert sha((V/name).read_bytes())==digest,name
    assert sha((F/'steiner-profiles-lean.zip').read_bytes())==report['freeze_sha256']
    assert report['pages_inspected']==sum(d['pages'] for d in docs)
    inventory=load(P/'04_integrity/MANIFEST.json')
    present={f.relative_to(P).as_posix() for f in P.rglob('*') if f.is_file() and '__pycache__' not in f.parts}
    assert set(inventory)|{'04_integrity/MANIFEST.json'}==present
    for n,h in inventory.items():assert sha((P/n).read_bytes())==h,n
    with checked_archive(ROOT/'archives/SteinerProfiles_preprint_v1.0.zip') as z:
        files={P.relative_to(ROOT).as_posix()+'/'+n for n in present}
        assert set(z.namelist())==files and len(z.namelist())==len(files) and z.testzip() is None
        for n in files:assert z.read(n)==(ROOT/n).read_bytes(),n
    print(json.dumps({'status':'PASS','paper':'STEINER-PROFILES','version':'1.0','pages':sum(d['pages'] for d in docs),'modules':162,'project_declarations_replayed':1997,'package_files':len(present)}))

if __name__=='__main__':
    verify()
