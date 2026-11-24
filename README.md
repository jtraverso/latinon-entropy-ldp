# Combinatorial entropy and counting — preprint series

Juan Pablo Traverso Gianini

The series contains three papers and a research note. Each edition includes an English manuscript, a Spanish translation, its Lean sources and an internal audit. [Series catalogue](SERIES.md).

| | Preprint 1.0 |
|---|---|
| Paper I | [Entropy and large deviations for Latin squares](preprints/LATINON) |
| Research note | [The kernel and measure representations of Latinons agree](preprints/GHHSBRIDGE) |
| Paper II | [Counting Steiner triple systems and Latin squares with prescribed color statistics](preprints/COLORSTATS) |
| Paper III | [Counting Steiner designs with prescribed color profiles](preprints/STEINER-PROFILES) |

## Paper I. Entropy and large deviations for Latin squares

Read the preprint on [alphaXiv](https://www.alphaxiv.org/abs/2611.latin-squares-entropy-large-deviations).

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

## Research note: the kernel and measure representations of Latinons agree

The Latinon preprint states and verifies its theorems in Lean for Latinons
described by measures; the conjecture of Garbe, Hancock, Hladký and Sharifzadeh is
written for Latinons described by kernels. The research note proves in Lean that
the two descriptions give the same Latinons, cut distance, pattern densities and
entropy, and so completes the Lean proof of their Conjecture 12.4 with their
definitions on the ground space [0,1] (entropy taken as minus relative entropy).

Read the research note on [alphaXiv](https://www.alphaxiv.org/abs/2611.latinons-kernel-measure-lean-formalization).

| Document | English | Español |
| --- | --- | --- |
| Research note | [PDF](preprints/GHHSBRIDGE/01_manuscript/ghhsbridge_en.pdf) · [Markdown](preprints/GHHSBRIDGE/01_manuscript/ghhsbridge_en.md) · [TeX](preprints/GHHSBRIDGE/01_manuscript/ghhsbridge_en.tex) | [PDF](preprints/GHHSBRIDGE/01_manuscript/ghhsbridge_es.pdf) · [Markdown](preprints/GHHSBRIDGE/01_manuscript/ghhsbridge_es.md) · [TeX](preprints/GHHSBRIDGE/01_manuscript/ghhsbridge_es.tex) |

[Paper directory](preprints/GHHSBRIDGE/README.md) ·
[Lean source freeze](preprints/GHHSBRIDGE/05_formalization/GHHSBridge_Lean_v1.0.zip) ·
[Freeze record](preprints/GHHSBRIDGE/02_validation/FREEZE.json).
Its seven Lean modules contain no `sorry`, and twelve axiom queries report only
`propext`, `Classical.choice` and `Quot.sound`. Read-only check:

```text
python scripts/verify_ghhsbridge.py
```

Reserved DOI https://doi.org/10.5281/zenodo.24293531 (deposit not yet published) ·
[Release](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/ghhsbridge-v1.0).

## Paper II: Counting Steiner triple systems and Latin squares with prescribed color statistics

Paper I counts Latin squares near a limit object. Paper II determines the
asymptotic number of Steiner triple systems, 1-factorizations and Latin squares
with exactly prescribed color statistics, with the rate given by relative
entropy, and deduces large-deviation principles for the type statistics of
random Steiner triple systems and 1-factorizations.

Read Paper II on [alphaXiv](https://www.alphaxiv.org/abs/2611.steiner-latin-squares-color-statistics).

| Document | English | Español |
| --- | --- | --- |
| Manuscript | [PDF](preprints/COLORSTATS/01_manuscript/color_stats_en.pdf) · [Markdown](preprints/COLORSTATS/01_manuscript/color_stats_en.md) · [TeX](preprints/COLORSTATS/01_manuscript/color_stats_en.tex) | [PDF](preprints/COLORSTATS/01_manuscript/color_stats_es.pdf) · [Markdown](preprints/COLORSTATS/01_manuscript/color_stats_es.md) · [TeX](preprints/COLORSTATS/01_manuscript/color_stats_es.tex) |
| Formal companion | [PDF](preprints/COLORSTATS/05_formalization/formal_companion_en.pdf) · [Markdown](preprints/COLORSTATS/05_formalization/formal_companion_en.md) | [PDF](preprints/COLORSTATS/05_formalization/formal_companion_es.pdf) · [Markdown](preprints/COLORSTATS/05_formalization/formal_companion_es.md) |

[Paper directory](preprints/COLORSTATS/README.md) ·
[Lean source freeze](preprints/COLORSTATS/05_formalization/ColorStats_Lean_v1.0.zip) ·
[Freeze record](preprints/COLORSTATS/05_formalization/FREEZE.json) ·
[Review guide](preprints/COLORSTATS/02_validation/release/REVIEW_GUIDE.md).
Its Lean freeze (57 modules) covers the upper bounds of the main theorems and the
finite algebra of Sections 5.8–5.10; 89 axiom queries report only `propext`,
`Classical.choice` and `Quot.sound`. The lower bounds are proved only in the
paper. Read-only check:

```text
python scripts/verify_colorstats.py
```

Reserved DOI https://doi.org/10.5281/zenodo.24308221 (deposit not yet published) ·
[Release](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/colorstats-v1.0).

## Paper III. Counting Steiner designs with prescribed color profiles

For a fixed partition of the points into color classes, Paper III counts labeled Steiner designs with exactly prescribed interior block-type quotas for every fixed block size at least three. The enumeration gives a large-deviation principle for the profile of a uniformly chosen design.

[English PDF](preprints/STEINER-PROFILES/01_manuscript/steiner_profiles_en.pdf) · [Spanish PDF](preprints/STEINER-PROFILES/01_manuscript/steiner_profiles_es.pdf) · [Formal companion](preprints/STEINER-PROFILES/05_formalization/formal_companion_en.pdf) · [Lean sources and proof catalogue](preprints/STEINER-PROFILES/05_formalization/steiner-profiles-lean.zip) · [Internal audit](publication/STEINER_PROFILES_RELEASE_AUDIT.json) · [Release](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/steiner-profiles-v1.0) · [DOI](https://doi.org/10.5281/zenodo.24501236).

## Licenses and status

The manuscripts and companions use [CC BY 4.0](LICENSE.md). The Lean sources
retain their upstream licenses. The Zenodo DOI https://doi.org/10.5281/zenodo.24284129 is reserved; the deposit is not yet published. No journal acceptance is claimed.

[Edition downloads](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/latinon-v1.0) ·
[Audit guide](publication/REVIEW_GUIDE.md) · [Attribution](NOTICE.md).
