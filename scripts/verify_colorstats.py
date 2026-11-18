"""Read-only verification of the COLORSTATS paper (Paper II) and its archive; no network, no Lean.

Checks the paper manifest, the bindings between Markdown, TeX and PDF recorded in the typesetting records, the bilingual
parity record, the Lean freeze record with its archive and logs, the release audit and proof ledger, the Zenodo
reservation, the catalogue entry and the complete package archive. It is not a mathematical review.
"""
from pathlib import Path
import hashlib, json, zipfile

ROOT = Path(__file__).resolve().parents[1]
B = Path('preprints/COLORSTATS')
ARCHIVE = Path('archives/ColorStats_preprint_v1.0.zip')
STANDARD = ['propext', 'Classical.choice', 'Quot.sound']
sha = lambda b: hashlib.sha256(b).hexdigest()
digest = lambda p: sha((ROOT/p).read_bytes())
read = lambda p: json.loads((ROOT/p).read_text(encoding='utf-8'))


def check():
    present = sorted(p.relative_to(ROOT/B).as_posix() for p in (ROOT/B).rglob('*') if p.is_file())
    manifest = read(B/'04_integrity/MANIFEST.json')
    assert manifest['paper'] == 'COLORSTATS' and manifest['version'] == '1.0'
    assert set(manifest['files']) == set(present) - {'04_integrity/MANIFEST.json'}
    for name, h in manifest['files'].items():
        assert digest(B/name) == h, name
    # Documents
    ts = read(B/'02_validation/TYPESETTING.json')
    assert [d['language'] for d in ts['documents']] == ['en', 'es']
    for d in ts['documents']:
        for key in ('source', 'tex', 'pdf', 'final_log'):
            assert digest(B/d[key]) == d[key + '_sha256'], d[key]
        assert d['undefined_references'] == 0 and d['missing_characters'] == 0
    parity = read(B/'02_validation/PARITY.json')
    assert parity['status'] == 'PASS' and all(parity['checks'].values())
    assert parity['en_sha256'] == digest(B/'01_manuscript/color_stats_en.md')
    assert parity['es_sha256'] == digest(B/'01_manuscript/color_stats_es.md')
    # Formalization
    fr = read(B/'05_formalization/FREEZE.json')
    assert fr['status'] == 'PASS' and fr['sorryAx'] is False and sorted(fr['axioms_reported']) == sorted(STANDARD)
    assert digest(B/'05_formalization'/fr['archive']) == fr['archive_sha256']
    assert digest(B/'05_formalization'/fr['axiom_log']) == fr['axiom_log_sha256']
    with zipfile.ZipFile(ROOT/B/'05_formalization'/fr['archive']) as z:
        files = [n for n in z.namelist() if not n.endswith('/')]
        assert set(files) == set(fr['entries_sha256']) and z.testzip() is None
        for n in files:
            assert n.startswith('lean/') and '.lake' not in Path(n).parts
            assert not n.endswith(('.olean', '.ilean')) and sha(z.read(n)) == fr['entries_sha256'][n], n
        for n in files:
            if n.endswith('.lean') and not n.startswith('lean/checks/'):
                text = z.read(n).decode('utf-8')
                assert 'sorry' not in text.replace('sorryAx', '') or n.endswith(('Challenge.lean', 'Statements.lean')), n
    tc = read(B/'05_formalization/TYPESETTING_COMPANION.json')
    for d in tc['documents']:
        for key in ('source', 'tex', 'pdf', 'final_log'):
            assert digest(B/'05_formalization'/d[key]) == d[key + '_sha256'], d[key]
        assert d['missing_characters'] == 0
    # Audit records
    audit = read(B/'02_validation/release/COLORSTATS_RELEASE_AUDIT.json')
    assert audit['status'] == 'PASS_INTERNAL_RELEASE_AUDIT' and audit['version'] == '1.0'
    assert all(v == 'PASS' for v in audit['checks'].values()) and audit['open_findings_minor_or_higher'] == 0
    for name, h in audit['records_sha256'].items():
        assert digest(B/name) == h, name
    ledger = read(B/'02_validation/release/PROOF_LEDGER.json')
    assert ledger['status'] == 'PASS_TARGETED_WRITTEN_REVIEW'
    assert digest(B/ledger['manuscript']) == ledger['manuscript_sha256']
    for key in ('round_3', 'round_4', 'round_5'):
        assert (ROOT/B/ledger[key]).is_file(), key
    # Reservation, manuscripts and catalogue
    res = read(B/'02_validation/ZENODO_RESERVATION.json')
    assert res['status'] == 'RESERVED_NOT_PUBLISHED' and res['submitted'] is False
    doi = res['doi']
    assert doi == '10.5281/zenodo.' + str(res['id'])
    for lang, word in (('en', 'Repository'), ('es', 'Repositorio')):
        text = (ROOT/B/f'01_manuscript/color_stats_{lang}.md').read_text(encoding='utf-8')
        assert 'DOI: https://doi.org/' + doi + '.' in text
        assert word + ': https://github.com/jtraverso/latinon-entropy-ldp.' in text
    index = read('PUBLICATION_INDEX.json')
    entry = [p for p in index['papers'] if p['id'] == 'COLORSTATS']
    assert len(entry) == 1 and entry[0]['doi'] == doi and entry[0]['version'] == '1.0'
    assert entry[0]['directory'] == B.as_posix() and entry[0]['doi_status'] == 'reserved_not_published'
    # Complete package archive
    sidecar = (ROOT/(ARCHIVE.as_posix() + '.sha256')).read_text(encoding='utf-8').strip()
    assert sidecar == digest(ARCHIVE) + '  ' + ARCHIVE.name
    with zipfile.ZipFile(ROOT/ARCHIVE) as z:
        names = set(z.namelist())
        assert len(names) == len(z.namelist()) and z.testzip() is None
        assert names == {(B/n).as_posix() for n in present}, sorted(names ^ {(B/n).as_posix() for n in present})[:5]
        for n in names:
            assert sha(z.read(n)) == digest(n), n
    return {'status': 'PASS', 'paper': 'COLORSTATS', 'version': '1.0', 'doi': doi, 'package_files': len(present),
            'documents': len(ts['documents']), 'parity': parity['counts'], 'lean_modules': fr['number_of_modules'],
            'axiom_queries': fr['print_axioms_queries'], 'axioms': STANDARD, 'archive_sha256': digest(ARCHIVE),
            'scope': 'Read-only verification of delivered bytes and records; does not invoke Lean or TeX and is not independent peer review'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
