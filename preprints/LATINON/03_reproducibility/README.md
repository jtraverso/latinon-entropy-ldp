# Reproducing preprint 1.0

The bilingual Markdown files in `01_manuscript` and `05_formalization` are the
semantic sources. The layout authority is the official CDR Paper III TeX at
commit `d12d980f8c86d8795e9faa0c6bb274ee936c7c8e`.

## Verify the delivered edition

From the repository root:

```text
python scripts/verify_repository.py
python scripts/verify_release.py
```

Both commands are read-only and use Python's standard library. They check
the source ZIP, its 309 modules and three configuration/toolchain files,
retained reconstruction logs and query outputs, document bindings and package
integrity. They require no access to the development repository and do not run
Lean. The complete package ZIP has a SHA-256 sidecar in `archives/`.

## Independently rebuild Lean

Extract `preprints/LATINON/05_formalization/Latinon_Lean_v1.0.zip` into a new
directory. It contains the project `lean/`, licenses and provenance records.
Install the toolchain in `lean-toolchain`, then run these commands from the
extracted project, one at a time:

```text
lake exe cache get
lake build LatinonFormalization
lake env lean ReviewAxioms.lean
```

Keep the delivered `lake-manifest.json` when obtaining its pinned packages;
do not update dependency revisions. Check that its nine revisions agree with
the freeze before accepting a reproduction.
The pinned version is Lean 4.35.0; Mathlib is at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. No rc3 compatibility is claimed.
External package checkouts and their caches must be obtained normally; local
junctions from the original machine are not distributed.

The configured library has 309 explicit local targets. The canonical module
imports 298. To build only that module and its imports, use
`lake build +LatinonFormalization:olean` instead. It does not replace checking
all 309 configured targets or the separate `ReviewAxioms` module. The recorded
reconstruction built every explicit target serially from zero project objects
and retained every module log. Only external pinned caches were reused.

The eight selected queries are supplemented by queries in the modules for
lower semicontinuity, compactness and compact rate sublevels. Their actual
outputs and hashes are in `02_validation/CLEAN_REBUILD_AUDIT.json`. The
edition preparation reused this completed evidence; it did not rerun Lean.

## Rebuild the documents

Install Pandoc, Tectonic and the versions in `requirements-typesetting.txt`,
then run from the repository root:

```text
python scripts/typeset_preprint.py
python scripts/audit_documents.py
```

The script converts only the body, applies the retained CDR preamble, and
compiles each final TeX file twice. The document audit checks bilingual
formulas, protected identifiers, PDF links and geometry and renders every
page. Rendered pages require actual visual review before a new visual PASS.

Any source or template change invalidates its TeX, PDF, visual review, hashes
and containing archive. Rebuild and reseal all dependent artifacts before
claiming a revised package. An old checksum or audit does not certify new bytes.
