# Counting Steiner triple systems and Latin squares with prescribed color statistics

Paper II · Preprint 1.0 · Juan Pablo Traverso Gianini · 17 November 2026

DOI: [10.5281/zenodo.24308221](https://doi.org/10.5281/zenodo.24308221) (reserved; the deposit is not published).

alphaXiv: <https://www.alphaxiv.org/abs/2611.steiner-latin-squares-color-statistics>.

[Manuscript EN](01_manuscript/color_stats_en.pdf) · [Manuscrito ES](01_manuscript/color_stats_es.pdf) ·
[Formal companion](05_formalization/formal_companion_en.pdf) · [Documento formal complementario](05_formalization/formal_companion_es.pdf)

[Lean source freeze](05_formalization/ColorStats_Lean_v1.0.zip) ·
[Freeze record](05_formalization/FREEZE.json) ·
[Mapping notes](05_formalization/MAPPING_NOTES.md) ·
[Review guide](02_validation/release/REVIEW_GUIDE.md) ·
[Proof ledger](02_validation/release/PROOF_LEDGER.json) ·
[Release audit](02_validation/release/COLORSTATS_RELEASE_AUDIT.json) ·
[Audit records](02_validation/audit) ·
[Editorial report](02_validation/EDITORIAL_REPORT.md) ·
[Bilingual parity](02_validation/PARITY.json) ·
[Reproduction](03_reproducibility/README.md) ·
[Integrity manifest](04_integrity/MANIFEST.json).

Paper II of the series *Combinatorial entropy and counting* (see the
[series catalogue](../../SERIES.md)). Paper I, *Entropy and large deviations for
Latin squares* (`LATINON`), counts Latin squares near a limit object; this paper
determines the asymptotic number of Steiner triple systems, 1-factorizations and
Latin squares with exactly prescribed color statistics, with the rate given by
relative entropy, and deduces large-deviation principles for the type statistics
of random Steiner triple systems and 1-factorizations.

The Markdown files are the semantic source; the TeX and PDF files are generated
from them by `03_reproducibility/typeset_paper.py` with the series layout. The
English and Spanish editions carry the same statements, formulas, citations and
numbering; `02_validation/PARITY.json` records the check.

The written proofs were reviewed by independent agents in five rounds
(`02_validation/audit`): a full line-by-line round over five scopes, a second
round over the corrected text, a closing round, and two targeted rounds on the
later editorial changes, the series framing and the formalization paragraph. The
last round reports no open finding of severity MENOR or higher. The external
theorems T and T⁺, the matching theorems of Ehard–Glock–Joos and of
Glock–Joos–Kim–Kühn–Lichev, Freedman's inequality and the inputs from the CDR III
preprint are used as black boxes with their hypotheses checked. This internal
review is distinct from journal peer review.

`05_formalization` holds the Lean source freeze (`ColorStats_Lean_v1.0.zip`,
57 modules), its freeze record, build and axiom logs, the mapping notes and the
formal companion in both languages. The formalization covers the upper bounds of
the main theorems and the finite algebra of Sections 5.8–5.10; the lower bounds
are proved only in the paper. The archive depends on pinned Mathlib and on the
Lean sources of the CDR III preprint, neither of which is bundled. Read-only
check, from the repository root:

```text
python scripts/verify_colorstats.py
```

The edition and release tag (`colorstats-v1.0`) are independent of the other
articles of the series; this paper adds files and catalogue entries and changes
no file of the Latinon paper or of the research note.
