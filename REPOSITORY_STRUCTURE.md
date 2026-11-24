# Series repository structure

The catalogue and per-paper edition policy are in `SERIES.md`. The initial
paper ID is `LATINON`; later published articles use sibling directories under
`preprints/`, with independent freezes, audits, archives and release tags.

The five-part layout follows CDR Paper III at the official series commit
`d12d980f8c86d8795e9faa0c6bb274ee936c7c8e`:

- `preprints/LATINON/01_manuscript/`: English and Spanish Markdown, generated TeX and compiled PDFs.
- `preprints/LATINON/02_validation/`: the original clean reconstruction and the subsequent incremental evidence; `v1.0/` holds the edition's document, semantic, freeze and visual checks.
- `preprints/LATINON/03_reproducibility/`: reproduction instructions and the CDR layout preambles.
- `preprints/LATINON/04_integrity/`: the paper's file manifest.
- `preprints/LATINON/05_formalization/`: bilingual companions and the portable source-only Lean freeze.

The research note `preprints/GHHSBRIDGE/` uses the same five parts. Its
validation folder holds the freeze record, the Lean build log and axiom output
(`02_validation/lean/`), the typesetting and document audits, the editorial report
and the Zenodo reservation; its integrity folder holds the package manifest.
The note has no separate formal companion: the correspondence between numbered
results and Lean declarations is Section 7 of the note.

Paper II, `preprints/COLORSTATS/`, uses the same five parts. Its validation folder
holds the audit records of the review rounds (`02_validation/audit/`), the release
audit, proof ledger and review guide (`02_validation/release/`), the bilingual parity
record, the typesetting records and the Zenodo reservation; its formalization folder
holds the source-only Lean freeze with its record and logs, the mapping notes and
the bilingual formal companion.

`publication/` contains the Latinon edition audit, proof ledger, source/provenance
checks and bibliography review. `scripts/` contains document tools and
read-only verifiers. `archives/` contains the complete package of each paper and its
SHA-256 sidecar. The source ZIP contains its own `lean/` project directory;
there is no second mutable source tree at repository root.

The original reconstruction records retain their relative paths and bytes.
The baseline source ZIP is in `02_validation/baseline/`; the current source
ZIP is in `05_formalization/`. The two snapshots are checked separately.
The edition verifier reads sources inside the portable ZIP when a retained
record refers to `lean/`. It requires neither private Git objects nor the
original machine's dependency junctions. Local build objects, dependency
caches, runtime files and development manuscript versions are excluded.

Verification is per paper. `scripts/verify_repository.py` and
`scripts/verify_release.py` cover LATINON: the files of the Latinon paper and its
audit must equal the entries of its sealed archive, while repository catalogue
files (README, series catalogue, index, citations, root manifest, scripts) may
grow with later papers and are checked inside the archive and through the root
manifest. `scripts/verify_ghhsbridge.py` covers GHHSBRIDGE. Each release tag keeps
its paper's edition exactly as released.

Operational visibility is separate from edition metadata. The same files can
undergo final audits with restricted access and subsequently be made public
without rewriting the manuscript or companion.

Paper III follows the five-directory series layout in [STEINER-PROFILES](preprints/STEINER-PROFILES/README.md).
