# Reproduction: GHHSBRIDGE preprint 1.0

## Lean

The sources are in `../05_formalization/GHHSBridge_Lean_v1.0.zip`. They depend on the
Lean sources of Latinon preprint 1.0, `Latinon_Lean_v1.0.zip`
(SHA-256 `567ac3561332351313d176018f5d41e475f88bfbd031cf05dad6b448635cfe81`), with
Lean 4.35.0 and Mathlib at commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Extract the two archives into sibling directories, so that the layout is

```text
<dir>/GHHSBridge_Lean_v1.0/lean
<dir>/Latinon_Lean_v1.0/lean
```

Set up the Latinon package as its own README describes, so that
`Latinon_Lean_v1.0/lean/.lake/packages` exists. Then run, in
`GHHSBridge_Lean_v1.0/lean`, one command after the other:

```text
lake build GHHSBridge
lake env lean ReviewAxioms.lean
```

The root `GHHSBridge.lean` imports the seven modules, so the first command reaches all
of them. The second prints the axioms of twelve declarations; each line is expected to
end with `[propext, Classical.choice, Quot.sound]`.

## Recorded evidence

`../02_validation/lean/build_GHHSBridge.log` and `review_axioms.log` are the outputs of
those two commands for this edition. In that run the seven modules and the root were
compiled from scratch; all other jobs were replayed from existing compiled objects of
the Latinon sources and of Mathlib. `../02_validation/FREEZE.json` records the source
hashes, the static checks (no `sorry`, no declared axioms, no `native_decide`), the
comparison of the Latinon tree used with the released archive, and the hashes of the
two logs. A fresh reconstruction of the whole dependency tree was not run for this
edition; the Latinon package records its own.

## Documents

`typeset_note.py` generates the two TeX/PDF documents from the Markdown sources in
`../01_manuscript` and the series layout in `layout/`, which is copied unchanged from
Latinon preprint 1.0. It uses Pandoc for the body and Tectonic for two compilation
passes. `audit_note.py` checks bilingual parity, the identifiers named in the note
against the frozen sources, the text layer and links of the PDFs, and renders every
page. `freeze_lean.py` packages the Lean sources and writes `FREEZE.json` without
running Lean. `seal_note.py` is run last: it writes `../04_integrity/MANIFEST.json`
and the package archive with its checksum sidecar.
