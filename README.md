# Combinatorial entropy and counting — preprint series

Juan Pablo Traverso Gianini

A series of independently versioned preprints with bilingual manuscripts, Lean
source freezes and per-paper audit records. The catalogue currently contains one
article: **Entropy and large deviations for Latin squares**, preprint 1.0.
See [Series catalogue and publication policy](SERIES.md).

This preprint proves a large deviation principle for uniform labeled Latin
squares in the full ordered Latinon distance, with speed n² and relative-entropy
rate. It deduces finite-pattern counting and applications to labeled bipartite
factorizations and completed CDR families with distinguished Latin blocks.
The CDR application counts a family with a fixed residue and a supplied
completed base. The manuscripts have not undergone journal peer review.

| Document | English | Español |
| --- | --- | --- |
| Manuscript | [PDF](preprints/LATINON/01_manuscript/latinon_en.pdf) · [Markdown](preprints/LATINON/01_manuscript/latinon_en.md) · [TeX](preprints/LATINON/01_manuscript/latinon_en.tex) | [PDF](preprints/LATINON/01_manuscript/latinon_es.pdf) · [Markdown](preprints/LATINON/01_manuscript/latinon_es.md) · [TeX](preprints/LATINON/01_manuscript/latinon_es.tex) |
| Formal companion | [PDF](preprints/LATINON/05_formalization/formal_companion_en.pdf) · [Markdown](preprints/LATINON/05_formalization/formal_companion_en.md) | [PDF](preprints/LATINON/05_formalization/formal_companion_es.pdf) · [Markdown](preprints/LATINON/05_formalization/formal_companion_es.md) |

[Lean source freeze](preprints/LATINON/05_formalization/Latinon_Lean_v1.0.zip) ·
[Internal audit](publication/LATINON_RELEASE_AUDIT.json) ·
[Proof ledger](publication/PROOF_LEDGER.json) ·
[Repository structure](REPOSITORY_STRUCTURE.md) · [Citation](CITATION.md).

The current source freeze has **310 local targets**, with **299 modules** in
the canonical import closure. An incremental cached build and all **twelve
axiom queries** passed, reporting only `propext`, `Classical.choice` and
`Quot.sound`. The package also retains the original clean 309-target
reconstruction and its original source archive. The additive refinement gives
residual diameter at most five and correction coefficient 5/2; the numbered
theorems and their existing consumers retain their original valid bounds.

From the repository root, run:

```text
python scripts/verify_repository.py
python scripts/verify_release.py
```

These read-only verifiers check the delivered bytes, all source-archive entries,
the completed reconstruction logs, axiom outputs, mathematical preservation,
document bindings and package hashes. They do not invoke Lean or constitute
independent mathematical peer review. [Reconstruction and document instructions](preprints/LATINON/03_reproducibility/README.md)
give the commands for rebuilding on another machine.

Each paper has its own version, audit, source archive and release tag. Only the
Latinon paper and its supporting evidence are included in the initial edition.
Development manuscripts and their Git history are kept separately. The
publication layout follows the author's official CDR preprint repository.
Repository visibility controls access; changing it does not change the edition's
mathematical content or the scope of its internal audit.

The manuscripts and companions use [CC BY 4.0](LICENSE.md). The Lean sources
retain their upstream licenses. The Zenodo DOI https://doi.org/10.5281/zenodo.24284129 is reserved; the deposit is not yet published. No journal acceptance is claimed.

[Edition downloads](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/latinon-v1.0) ·
[Audit guide](publication/REVIEW_GUIDE.md) · [Attribution](NOTICE.md).
