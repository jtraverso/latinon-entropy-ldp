# Reproduction

## Documents

`typeset_paper.py` converts `01_manuscript/color_stats_{en,es}.md` to TeX with
Pandoc 3.12.1 and compiles each PDF twice with Tectonic, using the series layout
files in `layout/` (copied unchanged from the GHHSBRIDGE note of the series).
Run from this directory's parent:

```text
python -I 03_reproducibility/typeset_paper.py en es
```

The script writes `02_validation/TYPESETTING.json` with the hashes of the source,
TeX, PDF and logs. Fonts are Latin Modern (OpenType). Rebuilding on another
machine gives the same TeX; the PDF bytes may differ by timestamps and font
paths.

`typeset_companion.py` does the same for the formal companion in
`05_formalization` (monospace font Consolas for the Lean identifiers).

## Lean formalization

`05_formalization/ColorStats_Lean_v1.0.zip` is a source-only freeze (top folder
`lean/`, with `source_manifest.json` and `DEPENDENCIES.md`). It needs Lean
`v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` and the Lean
sources of the CDR III preprint (byte-identical to `CDRIII_Lean_v1.0.zip`),
built and placed at the relative path `../cdr-clean-20261113/snapshot/lean`
that `lakefile.toml` expects (see `DEPENDENCIES.md`). Then, from `lean/`:

```text
lake build ColourStats
lake env lean checks/Axioms.lean
```

`05_formalization/FREEZE.json` records the build (9030 jobs, 57 project
modules), a rebuild from the archive, and the 89 axiom queries. The log of a first
rebuild attempt that ran out of memory is not distributed; `FREEZE.json` keeps
its hash.

## Numerical checks

`numerics/` holds twelve scripts with their logs and a manifest. They check
finite instances of the identities and stated values of the paper (see
`numerics/README.md` for the mapping to statements). They are evidence on
samples, not part of any proof. Environment of the recorded run: Python 3.12.10,
numpy 2.5.1, scipy 1.16.1, sympy 1.14.0, networkx 3.6.1, python-sat 1.9.dev15.

The README of `numerics/` uses the statement numbers and names of the draft
in which the checks were recorded (for example Φ for the right inverses, now
written Ψ in the paper); its table maps each check to the current lemma.
