# Repository structure

The five-part layout follows CDR Paper III at the official series commit
`d12d980f8c86d8795e9faa0c6bb274ee936c7c8e`:

- `preprints/LATINON/01_manuscript/`: English and Spanish Markdown, generated TeX and compiled PDFs.
- `preprints/LATINON/02_validation/`: unchanged completed reconstruction evidence; `v1.0/` holds the edition's document, semantic, freeze and visual checks.
- `preprints/LATINON/03_reproducibility/`: reproduction instructions and the CDR layout preambles.
- `preprints/LATINON/04_integrity/`: the paper's file manifest.
- `preprints/LATINON/05_formalization/`: bilingual companions and the portable source-only Lean freeze.

`publication/` contains the edition audit, proof ledger, source/provenance
checks and bibliography review. `scripts/` contains document tools and
read-only verifiers. `archives/` contains the complete preprint package and its
SHA-256 sidecar. The source ZIP contains its own `lean/` project directory;
there is no second mutable source tree at repository root.

The original reconstruction records retain their relative paths and bytes.
The edition verifier reads sources inside the portable ZIP when a retained
record refers to `lean/`. It requires neither private Git objects nor the
original machine's dependency junctions. Local build objects, dependency
caches, runtime files and development manuscript versions are excluded.

Operational visibility is separate from edition metadata. The same files can
undergo final audits with restricted access and subsequently be made public
without rewriting the manuscript or companion.
