"""One read-only entry point to all twelve source-bound recorded axiom checks."""
import json
from verify_repository import P, check_evidence, read

def main():
    check_evidence()
    audit = read(P / '02_validation/incremental/INCREMENTAL_BUILD_STATUS.json')
    queries = [{'declaration': name, 'axioms': [x.strip() for x in axioms.split(',')],
                'log': 'preprints/LATINON/02_validation/incremental/axioms.stdout.log'}
               for name, axioms in audit['queries'].items()]
    print(json.dumps({'status': 'PASS_RECORDED_AXIOM_EVIDENCE',
        'scope': 'Verified retained logs, not a fresh Lean invocation',
        'query_count': len(queries), 'queries': queries}, indent=2))

if __name__ == '__main__':
    main()
