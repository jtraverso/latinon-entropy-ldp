# The kernel and measure representations of Latinons agree: a Lean formalization

Preprint 1.0 · Juan Pablo Traverso Gianini · 16 November 2026

DOI: [10.5281/zenodo.24293531](https://doi.org/10.5281/zenodo.24293531) (reserved; the deposit is not published).

[Research note EN](01_manuscript/ghhsbridge_en.pdf) · [Nota de investigación ES](01_manuscript/ghhsbridge_es.pdf)

[Lean freeze](05_formalization/GHHSBridge_Lean_v1.0.zip) ·
[Freeze record](02_validation/FREEZE.json) ·
[Document audit](02_validation/DOCUMENT_AUDIT.json) ·
[Reproduction](03_reproducibility/README.md).

The note gives a Lean proof of Proposition 2.3 of *Entropy and large deviations for
Latin squares* (paper `LATINON` of this repository): on the ground space [0, 1] the
measure representation of Latinons and the kernel model of Garbe, Hancock, Hladký and
Sharifzadeh define the same objects up to null sets, with the same cut distance,
pattern densities and signed entropy. It also states their Conjecture 12.4 with their
own definitions and derives it from Theorem 2.2 of the Latinon preprint. The
correspondence between the numbered results and the Lean declarations is in Section 7
of the note; there is no separate formal companion.

The Lean freeze has seven modules and an aggregate root. They were compiled from
scratch against existing compiled objects of the Latinon 1.0 sources and of Mathlib,
which were not recompiled in that run; the Latinon source tree used was compared file
by file with `Latinon_Lean_v1.0.zip`. Twelve axiom queries report only the standard
axioms. The recorded log and query output are in `02_validation/lean`.

This is a research note in the [series catalogue](../../SERIES.md). Its edition and
release tag (`ghhsbridge-v1.0`) are independent of the other articles.

The internal checks recorded here are distinct from independent peer review.
