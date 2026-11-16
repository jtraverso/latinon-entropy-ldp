# Entropy and large deviations for Latin squares

Juan Pablo Traverso Gianini · Preprint 1.0 · 16 November 2026

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

The source-bound reconstruction compiled all **309 local modules**. The eight
selected endpoint axiom queries and three additional good-rate queries report
only `propext`, `Classical.choice` and `Quot.sound`. The canonical entry imports
298 modules; the configured library has 309 explicit targets. Pinned external
Mathlib ecosystem caches were reused. No Lean proof source or configuration
was changed when preparing this edition, and no additional Lean build was run.

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

This repository contains preprint edition 1.0 and its supporting evidence.
Development manuscripts and their Git history are kept separately. The
publication layout follows the author's official CDR preprint repository.
Repository visibility controls access; changing it does not change the edition's
mathematical content or the scope of its internal audit.

The manuscripts and companions use [CC BY 4.0](LICENSE.md). The Lean sources
retain their upstream licenses. No DOI or journal acceptance is claimed.

[Edition downloads](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/v1.0) ·
[Audit guide](publication/REVIEW_GUIDE.md) · [Attribution](NOTICE.md).
