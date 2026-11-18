# Editorial report — color-statistics paper, preprint 1.0

**Verdict: `EDITORIALLY_READY`** for preprint 1.0 (17 November 2026). The content queries below were resolved by the author's
observations and by the three audit rounds; the release itself waits for the author's approval. Nothing was published.

## Inputs and outputs

| Item | File | SHA-256 |
|---|---|---|
| Baseline (research draft 7.13) | `editorial/baseline_draft_7_13.md` | `ed2f0578…cb9bf17e5` |
| Research draft after the pass (7.14) | `C:\cdr-bicolour-lean\docs\PAPER_COLOUR_STATS_DRAFT_20261114.md` | `b912a98f…427f46cd37` |
| Edited manuscript (semantic source) | `01_manuscript/color_stats_en.md` | `b5f8ab23…c7b86aff` |
| TeX | `01_manuscript/color_stats_en.tex` | `6b5d5541…c6d846cf` |
| PDF (52 pages) | `01_manuscript/color_stats_en.pdf` | `73591fa9…94e5ecc1` |
| Spanish edition | `01_manuscript/color_stats_es.md` | `eac835c0…2d872154` |
| TeX (ES) | `01_manuscript/color_stats_es.tex` | `820095d3…372ab049` |
| PDF (ES, 55 pages) | `01_manuscript/color_stats_es.pdf` | `050201b6…ba733789` |

Full hashes are in `02_validation/MANIFEST.json`; typesetting logs in `02_validation/typesetting/`.

## Profile
- **Journal:** Random Structures & Algorithms (author's choice). Final formatting to the RSA template is a later step; this PDF uses the series layout of the Latinon preprint.
- **Voice:** the Latinon preprint 1.0, with the author's guidance (purpose first, one idea per paragraph, no operational detail, objects named simply).
- **Series:** paper 2 of the series (author's decision); the catalogue renumbering is a release-time step.

## What changed
- Draft history, status markers (`[GATE …]`, `[Qk]`, `[CITE-CHECK …]`, `[LIT …]`) and claims-ledger references removed from the text; the open items they flagged are listed below.
- Math converted from Unicode to LaTeX; labels (1.1)–(1.6), (4.1)–(4.3), (5.1)–(5.4) kept as tags.
- Every section opens with its purpose; long patchwork passages restructured (Lemma 5.6, §5.1 constants, §5.10 cleanup and cover-down); bullet lists turned into prose where the content was identical.
- Citations renumbered by first appearance (31 references, all cited); reference entries in one format.
- Two references to the unpublished Lean project removed (`E2Swap.inLambda_repr`/`finrank_Lam2` in §5.9; `main_theorem_T_with_triangle_monitors` in Appendix A). Citations of published repositories kept.
- Per-part change logs: `editorial/parts/report_A.md` … `report_F.md`.

## Semantic integrity
An independent reviewer compared the edited text with the baseline: **PASS WITH ISSUES**. No change to any
statement, definition, hypothesis, constant, asymptotic order, labelled display, proof step or numerical claim
(exhaustive token diff after normalising LaTeX/Unicode and citation numbers; manual reading of §§1–5.6 and the
openers; all 106 citations matched in order and locator). Issues and their resolution:
1. §1.4 the deduction of (1.2) from [LAT, Thm 3.1] read as stated in [LAT] → now "this deduction is ours and is not stated in [9]".
2. §1.4 the locator [FK20, Lemma 3.5] was lost with its marker → restored as "a deduction of ours from [20, Lemma 3.5]" (lemma number still to verify, Q-A3).
3. §5.1 "for each term we give the place where it is used" over-promised (c_ρ ≤ 1/(16k) has no stated use) → "we record where their terms are used".
4. Title block names the author → confirm.
Not read by hand (token diff only): bodies of §§5.8–5.9, the proof of Lemma 5.19, internals of §§6.3/6.5, the appendices.

## Research corrections found during the pass (draft 7.14, ledger §25)
- §5.10: λ ≤ d₀⁵θ₀δ₀/100 (introduced in 7.13) does not imply the E_X exclusion bound when d₀²δ₀ > 25/72; now λ ≤ min{d₀³θ₀/300, d₀⁵θ₀δ₀/100}.
- §5.11: the step-3 condition is δ′ < 4/1001, not "δ′ < 0.004".

## Content queries for the author (consolidated from 41; grouped by priority)

**Mathematical, to settle before submission**
- F-11: §6.5 says the lattice of a rich tripartite host is exactly the set of balanced integer vectors; "rich" is defined only for K_m ∨ C_h and Lemma 6.5 proves only that 1_{E(H)} lies in the lattice.
- B-7/B-8: §5.4 Hall argument bookkeeping (A/B vs A_Y(v)/B_Y(v) and the bad set; |ι_Y(v)|; the larger-B_Y(v) case; the s′ vertices of R3; reserve edges at v used by other bad vertices; (2C + o(1))n^{1−θ}).
- C-2/C-3: Lemma 5.6 step 1: scope of "at every vertex" for both m^{1−1/1000} bounds; the type-count error m^{2−1/1000} is not derived (holds for δ′ = θ/20; say so).
- B-9: Lemma 5.4 needs |R| ≤ (1/2 + o(1))pn² to give |L| ≤ n^{2−δ′}.
- B-10: Corollary 5.3 has no written proof; its constant C is undefined there (and clashes with C of Theorem T).
- D-2: Lemma 5.16 norm bound stated without argument (routine).
- C-1: Lemma 5.5 proof, "≥ c_X − 1 + 2ζn², divided by c_X ≤ n" should read with 2ζn²/c_X ≥ 2ζn.
- E-3, E-6: §5.10 "We take δ′ < c₀/8" is automatic from §5.1; undefined λ_Y, m_Y(τ), bare d, u.
- B-1, B-2, B-3, B-4, B-5, B-6, C-4, D-1, D-3, D-4, D-5, E-4: minor (factor 2 vs 4/3 to spare; unused c_ρ ≤ 1/(16k); stage cross-reference; c ≥ 1 in R1; Step 5 presentation; O(d*/κ) term; sign of b_σ; "phase-2"; "three degrees of a pair"; compressed Cor 1.6 step; "the first part").

**Attribution and literature**
- A-1: verify [Kwa20, Thms 3.1 and 3.2]. A-3: verify [FK20, Lemma 3.5]. A-2: check that the step profile meets the hypotheses of [LAT, Thm 3.1].
- A-4: the search scope has no date and MathSciNet was not checked. F-4: the [MM17] Sudoku fraction was read only through its abstract.
- A-9, F-12: scope of "formalized in Lean [14; 16]" and of "the certified bound for N₀" (Appendix A).
- A-10: "Sudoku squares by Luria" has no reference. A-14: [LL13] cited for both STS and 1-factorization upper bounds.
- F-5, F-6, F-7: bibliography against published versions (missing pages/volumes; [LAT] DOI not yet resolving; Brégman, Egorychev–Falikman, Kim–Vu, Chernoff, Hoeffding without entries).

**Status the text no longer shows** (A-5, F-1, F-2, F-3, A-6, A-7)
- The reservations of the audits (G1'' "established with reservations", G3 "closed with reservations") and the ledger questions Q1–Q4 (Q2: Thm 1.1 hypothesis Q ≥ ζ; Q4: existence of admissible partitions in Cor 1.4) are recorded in the ledger only. Decide whether the paper should state any of them.

**Notation** (A-11, F-8, F-9, F-10, E-5, B-7 and the boundary notes): reused symbols (Q, P, M, s, B, C, T, K, E, λ, σ, γ, J, r, χ, ℓ, R); "pattern densities do not depend on the labelling" (A-12); §1.6 dependence list (A-13).

## Author observations of 17 November 2026 and series harmonization
Ten observations from the author's review were applied:
1. Abstract rewritten as connected prose, purpose first; claims unchanged (Theorem 1.2 counts labeled systems).
2. The "Search scope" paragraph removed; one sentence ("To the best of our knowledge, Theorems 1.1 and 1.2 and Corollary 1.4 have not appeared before.") closes §1.4, keeping the results it names.
3. §1.1 merged into one sentence ("Classically, …"), keeping which bound is due to whom; §1.5 "runs this scheme" → "adapts this framework" / "carries out the analogous argument".
4. Remark 4.3: "awkward" → "difficult" (not "obstructed", which would claim impossibility), with the route through K_{n,n,n} named.
5. §4.2 Steps 4 and 5 with run-in titles (class entropy; candidate count) instead of announcing sentences.
6. Openers of §§5.8, 5.9, 5.10 and 6 varied; the same template removed from §§2, 4, 5.7 and 5.11.
7. Nash–Williams parenthesis rewritten as a sentence; meaning unchanged.
8. `paperIIITowerThreshold` removed from Remark 5.22 ("an explicit tower function, recorded in [14]").
9. §7 introduction and the §8 filler sentence removed; Remark 7.1 merged into one sentence; Remark 7.3 "report" → "state". **Content query:** the proposal "proved that" would strengthen a citation claim on [19], which was read only through its abstract; change it once the full text is checked.
10. Open problems in prose; "other designs" kept (the proposal "general t-designs" would widen the problem).

Series harmonization: American spelling as in the Latinon paper (title now "… prescribed color statistics"; color, labeled, bicolored, normalized, neighborhood, center, minimize, …; cited titles keep their spelling, e.g. Keevash's *Coloured and directed designs*); reference entries in the Latinon format with arXiv and DOI links. The pipeline is `editorial/build.py`.
These edits were checked against the baseline by the editor; they do not touch any statement, display or constant.

## Tables and figure (added at the author's request)
Evaluated against the series practice (the Latinon paper has one figure and one table of choices) and kept only where they carry the narrative:
- **Table 1** (end of §1.3): the counting results — objects, prescribed counts, logarithm of the count, error — for Theorems 1.1, 1.2, 1.5, 1.7, 1.9 and Corollary 1.11; the caption records Proposition 1.3, Theorem 1.10 and Corollaries 1.6, 1.8. Every entry restates a statement of §1.
- **Figure 1** (§5.1, TikZ, vector): schematic of the vortex construction — the four stages and the sets they use (R for cleanup, F and R′ for cover-down, E_X for the exchanges inside U). Marked "not to scale"; §1.5 points to it.
- **Table 2** (§5.1): order of choice of the constants, with what each row is chosen from and where it is used — the analogue of the Latinon table of choices; it makes the absence of circularity visible.
- Not added: a table of the Remark 7.2 minimisations and a comparison table for §1.4 (the text already carries both clearly).
These additions were checked against the statements by the editor, not by the independent semantic reviewer.

## Audit to PASS and preprint 1.0
- Three audit rounds by independent agents at the standard of paper 1 (`02_validation/audit`): round 1 over five scopes, round 2 over
  the corrected text, round 3 closing with **PASS** (no open finding of MENOR or higher). Every fix was applied to the parts
  (`editorial/parts/edited_*.md`) by recorded scripts (`editorial/fix_round2.py`, `fix_round2b.py`, `fix_round3.py`) and the
  manuscript rebuilt. After round 3 the last sentence of Lemma 6.5 was completed ("is an integer combination of triangles of $H$"),
  a clarification reported by the translator.
- Front matter: Preprint 1.0 — 17 November 2026; DOI 10.5281/zenodo.24308221 (reserved, unpublished draft); repository line.
- Spanish edition `01_manuscript/color_stats_es.md`, written from the English (`editorial/es/`: brief, chunks, harmonization patch,
  assembly with parity check). Parity PASS (`02_validation/PARITY.json`).

## Author's second editorial round, formalization and round 4
- Applied by `editorial/fix_author2.py` (EN) and `editorial/es/patch_es_author2.py` (ES): abstract split; §1.1 index paragraph;
  sentence after Corollary 1.11; opening of §6; "So" replaced by Hence/Thus/Therefore/Consequently (no "So" remains). Kept from the
  locked text: P₀ is the type law of a uniformly random triple; the full type law P; the definition of the outline.
- The four suspected OCR errors are extraction artifacts (checked in the rendered PDF).
- Lean freeze `05_formalization/ColorStats_Lean_v1.0.zip` (57 modules, 89 axiom queries, standard axioms only), formal companion
  EN/ES, mapping notes. New §1.7 (`editorial/fix_formalization.py`, ES `patch_es_formalization.py`); Lemmas 5.17 and 5.20 say
  "integer combination", as in Lean.
- Round 4 (`02_validation/audit/R4_*`): three MENOR findings (§1.7 scope and error, the sentence after Corollary 1.11, the
  companion wording) and editorial items, applied by `editorial/fix_round4.py`; closure checked.

## Author's third editorial round (series framing, structure of the series papers, Spanish review)
Models read before editing: CDR III (`prescribed_en.md`, `prescribed_es.md`), the Nash-Williams Paper II, the Latinon preprint and
the GHHSBRIDGE note. English first (`editorial/fix_author3.py`), then Spanish (`editorial/es/patch_es_author3.py`, `…3b.py`).
- **Series framing.** Front line "Paper II. Combinatorial entropy and counting."; the abstract opens with Paper I [1] and the
  research note [2], as the CDR papers do, and is set in four short paragraphs. §1.4 cites the note. The references were renumbered
  by first appearance (`02_validation/audit/REFERENCE_NUMBERING.md`).
- **Formalization.** §1.7 removed. A one-paragraph section "Formal verification" before the acknowledgments points to the formal
  companion [38], as in CDR III and the Nash-Williams papers; the detail lives in the companion.
- **Acknowledgments** and **Use of artificial intelligence and computational tools** added, with the text of CDR III unchanged, including
  the paragraph on Certo and its reference [39] (author's instruction of 17 November 2026).
- **Tables and figures.** Evaluated again. Added Table 2 (§1.5): the five settings of the scheme with their host, right inverse,
  lattice lemma and exchanges; it replaces a paragraph of cross-references the reader had to hold in mind through §§5.8–6. The
  constants table is now Table 3. Considered and not added: a drawing of the Pasch trade and of the intercalate exchange (the
  two block sets are already displayed in the lemmas and a picture adds no information), and a plot of the rate function (the
  paper uses only its value at the minimum).
- **Author's review of the English edition.** $Q$ in the abstract, "Constraints on κ", "For c ∈ U_C" and the DOI of [24] are
  correct in the source (extraction artifacts). Applied: "which we deduce from [25, Lemma 3.5]"; "directly" in the proof of Claim A;
  the clause on ν_XX < 1 in §5.3, justified by ν_XX ≤ 1 − p, and its counterpart in §5.9; "dividing the lower bound of Theorem 1.5
  … by #STS(n)" (a theorem is not divided), also at the end of §5.11. No sentence starting with "So" remains.
- **Author's review of the Spanish edition.** The five reported errata are extraction artifacts (source checked). Applied: the
  calques ("especie" → "modalidad", "contraparte de conteo" → "versión enumerativa", "ninguna determina a la otra", "piezas
  cuasialeatorias por arriba", "ni a las ternas arcoíris"), the abstract without bilingual glosses ("produce"), the Corollary 1.6
  sentence, varied openers where two consecutive sentences began with "Así," / "Por lo tanto,", and the clause on ν_XX.
- **Spanish terminology of the series** (definitive Spanish editions of CDR III and the Latinon paper): "tabla agregada" for
  outline, "completación", "grafo/grado residual" for leftover, "documento formal complementario" for the companion.

## Layout QA (after the last change)
- Tectonic, two passes; 0 missing characters; 1 overfull box(es) of about 2 pt (§5.9, cosmetic); 0 undefined references.
- All 52 pages rendered and scanned for flattened lists and replacement characters; the pages with the abstract, Table 1, Figure 1, Table 2, §§1.4, 5.4 and 5.11 and the references inspected visually.
- Spanish edition: 55 pages, 0 missing characters, 1 overfull box(es) of under 2 pt (Table 1, cosmetic); every page rendered (`02_validation/render_es`); title page, Tables 1–2, Figure 1, appendices and references inspected visually.
