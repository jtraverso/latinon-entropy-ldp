"""Read-only verification of the preprint and original reconstruction; no Lean."""
from pathlib import Path
import hashlib,json,re,zipfile
from urllib.parse import unquote,urlsplit

ROOT=Path(__file__).resolve().parents[1]
P=Path('preprints/LATINON');V=P/'02_validation/v1.0'
def sha(data):return hashlib.sha256(data).hexdigest()
def digest(path):return sha((ROOT/path).read_bytes())
def read(path):return json.loads((ROOT/path).read_text(encoding='utf-8'))

def check_evidence():
    freeze=read(V/'FREEZE.json');clean=read(P/'02_validation/CLEAN_REBUILD_AUDIT.json')
    assert freeze['version']=='1.0' and clean['status']=='PASS_SOURCE_BOUND_CLEAN_RECONSTRUCTION'
    assert digest(freeze['archive'])==freeze['sha256']
    assert digest(freeze['clean_reconstruction_audit'])==freeze['clean_reconstruction_audit_sha256']
    with zipfile.ZipFile(ROOT/freeze['archive']) as z:
        names=z.namelist();assert len(names)==len(set(names)) and z.testzip() is None
        assert set(names)==set(freeze['entry_sha256'])
        for name in names:
            assert name.startswith('lean/') and '..' not in Path(name).parts
            assert '.lake' not in Path(name).parts and '.git' not in Path(name).parts
            assert not name.endswith(('.olean','.ilean','.olean.private','.olean.server'))
            assert sha(z.read(name))==freeze['entry_sha256'][name],name
        manifest=json.loads(z.read('lean/source_manifest.json'))
        modules=manifest['modules'];assert len(modules)==309
        snapshots=[read(P/'02_validation/clean_run'/name) for name in ['SOURCE_BEFORE.json','SOURCE_AFTER.json']]
        assert snapshots[0]==snapshots[1]==freeze['source_configuration_files']
        assert set(snapshots[0])==set(modules.values())|{'lakefile.toml','lake-manifest.json','lean-toolchain'}
        for name,h in snapshots[0].items():assert sha(z.read('lean/'+name))==h,name
        for name,h in manifest['files_sha256'].items():assert sha(z.read('lean/'+name))==h,name
        assert z.read('lean/lean-toolchain').decode().strip()=='leanprover/lean4:v4.35.0'
        packages=json.loads(z.read('lean/lake-manifest.json'))['packages']
        assert len(packages)==9
        for package in packages:assert clean['external_package_commits'][package['name']]['commit']==package['rev']
        contracts=read('publication/audit/PROTECTED_CONTRACT_AUDIT.json')
        assert contracts['status']=='PASS' and len(contracts['items'])==21
        for item in contracts['items']:assert sha(z.read(item['delivered_source']))==item['source_sha256']
    done=read(P/'02_validation/clean_run/COMPLETED.json')
    assert set(done)==set(modules) and clean['local_module_targets']==309
    standard={'propext','Classical.choice','Quot.sound'}
    for module,item in done.items():
        assert item['exit_code']==0 and item['source_sha256']==snapshots[0][modules[module]]
        assert re.fullmatch('[a-f0-9]{64}',item['object_sha256'])
        log=P/'02_validation/clean_run'/item['log']
        assert digest(log)==item['log_sha256']
        text=(ROOT/log).read_text(encoding='utf-8-sig')
        assert re.search(r'Built '+re.escape(module)+r'\b',text),module
        assert not re.search(r'\berror:|sorryAx',text),module
        for axioms in re.findall(r"depends on axioms:\s*\[([^\]]*)\]",text):
            assert {x.strip() for x in axioms.split(',') if x.strip()}<=standard
    for name,key in [('SOURCE_BEFORE.json','source_before_sha256'),('SOURCE_AFTER.json','source_after_sha256'),('COMPLETED.json','completed_objects_log_sha256')]:
        assert digest(P/'02_validation/clean_run'/name)==clean[key]
    assert clean['initial_project_object_count']==0 and not clean['project_objects_restored']
    assert clean['source_config_before_after_identical'] and clean['one_project_target_at_a_time']
    assert len(clean['endpoint_queries'])==8 and len(clean['good_rate_queries'])==3
    text=(ROOT/clean['endpoint_query_log']).read_text(encoding='utf-8-sig')
    assert digest(clean['endpoint_query_log'])==clean['endpoint_query_log_sha256']
    found={name:{x.strip() for x in axioms.split(',') if x.strip()}
        for name,axioms in re.findall(r"info: ReviewAxioms\.lean:\d+:\d+: '([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)}
    assert set(found)==set(clean['endpoint_queries'])
    for name,axioms in clean['endpoint_queries'].items():assert set(axioms)==found[name]<=standard
    for name,item in clean['good_rate_queries'].items():
        assert digest(item['log'])==item['log_sha256']
        text=(ROOT/item['log']).read_text(encoding='utf-8-sig')
        values=re.findall(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",text)
        assert len(values)==1
        assert {x.strip() for x in values[0].split(',') if x.strip()}==set(item['axioms'])<=standard
    ledger=read('publication/PROOF_LEDGER.json')
    assert len(ledger['core_steps'])==23 and len(ledger['application_steps'])==8
    assert digest(ledger['current_clean_audit'])==ledger['current_clean_audit_sha256']
    for step in ledger['core_steps']:assert freeze['entry_sha256'][step['source']]==step['source_sha256']
    finite=read(P/'02_validation/FINITE_REGRESSIONS.json')
    assert finite['status']=='PASS' and digest('scripts/check_finite_identities.py')==finite['script_sha256']
    return {'compiled_modules':309,'canonical_import_closure':298,'endpoint_queries':8,
            'additional_good_rate_queries':3,'lean_source_archive_sha256':freeze['sha256'],
            'fresh_lean_build_in_this_edition':False}

def check_mathematics():
    old=read(V/'PROTECTED_BASELINE.json');records=[]
    for name,item in old['documents'].items():
        text=(ROOT/name).read_text(encoding='utf-8')
        statements=re.findall(r'^\*\*(?:Theorem|Lemma|Corollary|Proposition|Teorema|Lema|Corolario|Proposición) [^\n]+',text,re.M)
        assert statements==item['statements'],name
        assert re.findall(r'\$\$(.*?)\$\$',text,re.S)==item['displays'],name
        assert text[text.index('## 1.'):text.index('## 11.')]==item['mathematical_body_before_section_11'],name
        marker='## Appendix.' if name.endswith('_en.md') else '## Apéndice.'
        assert text[text.index(marker):]==item['appendix_and_references'],name
        assert 'Preprint 1.0' in text and not re.search(r'Private review candidate|Candidata privada|ongoing reconstruction|reconstrucción en curso',text)
        records.append({'source':name,'baseline_sha256':item['sha256'],'edition_sha256':digest(name),
            'unchanged_statements':len(statements),'unchanged_displays':len(item['displays']),
            'mathematical_sections_appendix_and_references_exactly_preserved':True})
    for name,item in old['companions'].items():
        text=(ROOT/name).read_text(encoding='utf-8')
        actual=re.findall(r'`(LatinonEntropy\.[^`]+)`',text)
        assert actual==item['declarations'],name
        assert 'Preprint 1.0' in text and not re.search(r'Private review candidate|Candidata privada|ongoing reconstruction|reconstrucción en curso',text)
    return records

def check_documents():
    typed=read(V/'TYPESETTING.json');doc=read(V/'DOCUMENT_AUDIT.json');visual=read(V/'VISUAL_REVIEW.json')
    assert typed['status']=='PASS_COMPILATION' and doc['status']=='PASS_STATIC_RENDERED_AWAITING_VISUAL'
    assert visual['status']=='PASS_ALL_RENDERED_PAGES'
    assert digest(V/'DOCUMENT_AUDIT.json')==visual['document_audit_sha256']
    assert len(typed['documents'])==len(doc['documents'])==4
    for item in typed['documents']:
        for key in ['source','tex','pdf']:assert digest(item[key])==item[key+'_sha256']
        for log in item['passes']:assert log['exit_code']==0 and digest(log['path'])==log['sha256']
        assert digest(item['final_log'])==item['final_log_sha256']
    for item in doc['documents']:
        observed=visual['documents'][item['pdf']]
        assert digest(item['pdf'])==item['pdf_sha256']==observed['pdf_sha256']
        assert observed['pages_inspected']==list(range(1,item['page_count']+1))
        assert observed['open_layout_issues']==[]
        for page in item['pages']:assert digest(page['image'])==page['sha256']==observed['rendered_page_sha256'][str(page['page'])]
    return {'documents':4,'rendered_pages':sum(d['page_count'] for d in doc['documents']),'parity':doc['parity']}

def check_metadata():
    index=read('PUBLICATION_INDEX.json')
    assert index['edition']=='1.0' and index['date']=='2026-11-16'
    assert index['repository']=='https://github.com/jtraverso/latinon-entropy-ldp'
    assert index['license']=='CC-BY-4.0' and len(index['papers'])==1
    assert index['papers'][0]['version']=='1.0' and index['papers'][0]['doi'] is None
    cff=(ROOT/'CITATION.cff').read_text(encoding='utf-8')
    assert 'version: "1.0"' in cff and 'date-released: 2026-11-16' in cff
    assert 'license: CC-BY-4.0' in cff and '\ndoi:' not in cff
    assert 'Creative Commons Attribution 4.0' in (ROOT/'LICENSE.md').read_text(encoding='utf-8')
    for folder in ['01_manuscript','02_validation','03_reproducibility','04_integrity','05_formalization']:
        assert (ROOT/P/folder).is_dir()
    assert not (ROOT/'lean').exists(),'Sources belong to the unchanged ZIP, not a second mutable tree'
    targets=0
    for path in ROOT.rglob('*.md'):
        if any(x in path.relative_to(ROOT).parts for x in ['tmp','.git']):continue
        for target in re.findall(r'\]\(([^)]+)\)',path.read_text(encoding='utf-8')):
            if urlsplit(target).scheme or target.startswith('#'):continue
            resolved=(path.parent/unquote(target.split('#',1)[0])).resolve()
            assert resolved.is_relative_to(ROOT) and resolved.exists(),(path,target)
            targets+=1
    return {'edition_metadata':'PASS','local_markdown_links_checked':targets}

def check():
    evidence=check_evidence();check_mathematics();documents=check_documents();metadata=check_metadata()
    audit=read('publication/LATINON_RELEASE_AUDIT.json')
    assert audit['status']=='PASS_INTERNAL_RELEASE_AUDIT' and audit['version']=='1.0'
    assert all(value=='PASS' for value in audit['checks'].values())
    for name,h in audit['evidence'].items():assert digest(name)==h,name
    manifest=read(P/'04_integrity/MANIFEST.json')
    for name,h in manifest.items():assert digest(P/name)==h,name
    lines=(ROOT/'manifest_sha256.txt').read_text(encoding='utf-8').splitlines()
    for line in lines:
        h,name=line.split('  ',1);assert digest(name)==h,name
    return {'status':'PASS','version':'1.0',**evidence,**documents,**metadata,
        'scope':'Delivered edition, original reconstruction evidence and observed document QA; no new Lean build or independent peer review'}

if __name__=='__main__':print(json.dumps(check(),indent=2))
