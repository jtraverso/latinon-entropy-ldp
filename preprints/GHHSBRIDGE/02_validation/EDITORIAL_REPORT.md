# Editorial report: GHHSBRIDGE preprint 1.0 (16 November 2026)

Protocol: `mathematical-paper-editor` (jtraverso/mathematical-paper-editor @ d46f0c94).

**Verdict: `EDITORIALLY_READY_WITH_QUERIES`.** The package is complete and sealed locally. It has not been
pushed, tagged or deposited; publication waits for the author's approval and for the queries below.

## Stage and authorities

- Mathematical source: Latinon preprint 1.0, Proposition 2.3 and Theorem 2.2; GHHS (Discrete Analysis 2023:8).
- Semantic sources: `01_manuscript/ghhsbridge_en.md`, `ghhsbridge_es.md`.
- Layout authority: `03_reproducibility/layout/series_{en,es}.tex`, unchanged from Latinon preprint 1.0.
- Formal evidence: `02_validation/FREEZE.json`, `02_validation/lean/`. The Lean sources did not change in this
  revision.

## Editorial line of this revision

The author's second review asked for a different editorial line: state the purpose first, give each paragraph
one idea, leave out operational detail, and write the Spanish version from the ideas instead of translating
sentence by sentence.

- **Purpose.** The Latinon preprint presents its counting theorem as a confirmation of Conjecture 12.4 of GHHS,
  but the theorem is stated and checked in Lean for measures, the conjecture is written for kernels, and the
  equivalence was proved on paper only. The note proves the equivalence, in Lean and with a written argument.
  The abstract and §1 now say exactly this, in this order.
- **Vocabulary.** "Kernel Latinon" and "measure Latinon" replace "kernel representation", "measure
  representation" and "Latinon in the sense of [1]".
- **Sections.** Each of §§2–6 opens with the idea in plain words (integrate and condition; same distance written
  with kernels or with measures; a density is a probability of a random configuration; entropy cell by cell
  against entropy on the cube; the conjecture is the counting theorem in the language of GHHS). Definitions,
  statement and proof follow.
- **Removed.** Build timing and rebuild instructions, the description of what was recompiled, the list of reading
  conventions, the remarks on radius and closed boxes, and the separate paragraph on finite densities. What is
  mathematically needed from them is kept in one clause where it is used (the relabelling maps in §3, the finite
  density in §6). The operational detail remains in `03_reproducibility/README.md` and `FREEZE.json`.
- **Spanish.** Written from the same paragraph plan, with the terms of the Spanish Latinon paper (núcleo, mapa de
  orden, reetiquetado, distancia de corte) and "marginal" for the marginals.

## Protected elements and semantic integrity

The numbered results are the same eight as before (Theorems 2.1, 3.1, 4.1, 5.2, 6.2, 6.3; Lemmas 5.1, 6.1), with
the same hypotheses and conclusions, and correspond to the same Lean declarations. Changes inside statements are
of wording only:

- Theorem 2.1(c), (d) are phrased as "passing to the kernel (measure) and back"; the content is unchanged
  (ν is recovered exactly; K is recovered almost everywhere; kernels equal almost everywhere with the same order
  map give the same measure).
- Theorems 3.1, 4.1, 5.2 write the measure Latinon explicitly as (ν_K, f) instead of W_L.
- "Absolutely continuous" is written as "has a density" in §5; these are equivalent for the σ-finite measures
  involved.
- §5 states KL(μ‖λ) = ∫ g log g "which may be infinite" instead of splitting the integrable and non-integrable
  cases; the two formulations agree because the negative part of g log g is bounded.
- The proof of Theorem 6.3 no longer names the penalty t + 1 and the error 1; the Lean proof is unchanged.

Formal-status sentences in §7 are supported by `FREEZE.json`: seven modules and a root, no `sorry`, no declared
axioms, twelve axiom queries reporting the three standard axioms. The statement that the dependencies were replayed
rather than recompiled in the recorded run is no longer in the note; it is in `FREEZE.json`, in the package README
and in `03_reproducibility/README.md`.

Symbols of GHHS were verified on rendered pages of the published PDF (formula (2) of Definition 4.3, page 22;
Conjecture 12.4, page 57). Errata reported in the first review were checked against source, TeX and render; only
the missing visible URL in reference [2] was real, and it is fixed.

Bilingual parity (`DOCUMENT_AUDIT.json`, status PASS): same sections, numbered results, equation tags, display
formulas, code identifiers, table rows and references in EN and ES; every Lean identifier named in the note
exists in the frozen sources and appears unbroken in the text layer of both PDFs. Final logs: no overfull box, no
undefined reference. All pages were rendered after the last compilation, and the pages of the Spanish version and
the first and table pages of the English version were inspected at reading resolution.

## Fourth round (author's text, acknowledgments, AI statement, DOI)

- **Author's wording.** The author's abstract and paragraphs for §1 (gap and conventions), the opening of the proof
  of Theorem 2.1, the quantifier-swap remark, §3, §4, the Mathlib remark in §5, §6 and §7 are incorporated in both
  languages. Four phrases were narrowed to what is proved: "in the exact setting of [1]" → "with the definitions of
  [1] on the ground space [0,1]" (the isomorphism to a general ground space is not formalized); "canonical
  correspondence" → "canonical correspondence up to null sets"; "minimizing" → "taking the infimum"; "the fiber is
  empty or consists solely of infinite-rate Latinons" → the same condition stated without "fiber" and "rate", which
  the note does not define. "Leaves the conditional case open" → "lists the conditional form as still to be done",
  and "a self-contained proof" → "a proof", since the proof uses Mathlib's kernel Radon–Nikodym derivative.
- **Section 7.** The Mathlib commit hash is no longer in the text; it remains in `lake-manifest.json`, `FREEZE.json`
  and `03_reproducibility/README.md`.
- **Acknowledgments and AI statement.** Copied from CDR Paper III (EN and ES), which names Claude (Anthropic),
  ChatGPT/Codex (OpenAI) and Certo; Certo is reference [4].
- **DOI.** Zenodo draft deposition 24293531, pre-reserved DOI 10.5281/zenodo.24293531, not submitted, no files
  (`02_validation/ZENODO_RESERVATION.json`). Reserved with the same API method used for Latinon and CDR Paper III
  (`docs/reserve_zenodo_ghhsbridge.py` in the working project). Printed under the date, as in the Latinon preprint;
  the typesetting script checks that the printed DOI equals the reservation.

## Open queries (owner: author)

| ID | Query |
|---|---|
| Q1 | Title and paper ID. The title describes the content (the two representations agree); a title that names the purpose (the equivalence with Conjecture 12.4) is possible. The title is also the title of the Zenodo draft. `GHHSBRIDGE` / `ghhsbridge-v1.0` are used throughout. |
| Q2 | Reference [2] omits the Latinon DOI 10.5281/zenodo.24284129, which still returned 404 on 16 November 2026 (reserved, deposit not published). The DOI of this note does not resolve either until its deposit is published. |
| Q3 | Reference [1] prints the DOI given on the published paper (10.19086/da.83253); the resolver returned 404 on the same date. The arXiv link resolves. Kept as printed by the journal. |
| Q4 | Resolved by the author: Certo is kept, with a description that fits this note (used in the work of [2], where it certified a constant of the transportation correction; `publication/audit/CONSTANTS_ASSESSMENT.md` of the Latinon edition). No computation is a premise of the note's results. |
| Q5 | Repository integration is not done: `SERIES.md`, `PUBLICATION_INDEX.json`, root README and citation files of the public repository are untouched. Proposed entries are in the working project (`docs/REPO_INTEGRATION.md`). |
