# Audit round 5 — the author's third editorial round (independent agents, read-only, 17 Nov 2026)

Scope: diff of the English and Spanish manuscripts against the version that passed round 4: series framing in the front block and
abstract, new Table 2 (five settings), removal of §1.7 and the new section "Formal verification", acknowledgments and AI-use
sections, two clauses on rescaled availability probabilities (§§5.3, 5.9), wording of Claim A and of two "dividing the bound"
sentences, renumbered references, Spanish terminology of the series, formal companions. Reference numbers are the final ones.

Verdict of the round: **NOT PASS** — three MENOR findings (wording), no SERIO or BLOQUEANTE; all applied (`editorial/fix_round5_en.py`,
`editorial/es/patch_es_round5.py`) and the closure checked (`R5_closure.md`).

| Item | Status |
|---|---|
| Front block and abstract | OK; claims about Paper I and the note match §1.4, [1] (Theorems 2.1, 2.2, 3.1, Lemma 7.1, Proposition 10.3) and [2]; "Unlike the counts of Paper I, which hold in a neighborhood…" exact |
| Table 2 | OK, all 30 cells (§§5.8 and 5.10 both use Lemma 5.20; §5.10 uses Pasch trades with Lemma 5.14 unchanged); Table 1/2/3 references correct in md, TeX, PDF, EN and ES |
| Formal verification | M1, M2; the rest supported by FREEZE.json, MAPPING_NOTES.md, both axiom logs and the companions; no reference to "Section 1.7" left |
| Clauses of §5.3 and §5.9 | OK: ν_XX = (1−p)(1−Σq) ≤ 1−p, φ = 1+O(1/n), p = n^{−δ′} ≫ 1/n; in §5.9 ν_XΓ ≤ 1−p because the cleanup reserve of density p also covers vertex–color pairs |
| Claim A, divisions | OK, no logical change |
| References | OK: [1]–[38] in order of first appearance; all 141 citations of the round-4 version match position by position after renumbering |
| Spanish content and citations | M3; otherwise equal to the English; citations and locators identical in all paragraphs |
| Spanish terminology | OK in the manuscript (no leftover of the old terms, no gender disagreement); E1 in the companion |
| Companions | consistent with the paragraph except M1; E1 |
| Regression | OK: 324 statement references, 116 section references, 13 equations, none dangling, EN and ES |

## Findings
- **M1 MENOR** "Formal verification": the error O(n^{7/4}) is false for the typical-graph bound, which also loses O(ηn²). Applied:
  "…carry $O(n^{7/4})$, plus the loss $O(\eta n^2)$ from typicality in Theorem 1.9(a)…", and the sentence on the form with Φ(t).
- **M2 MENOR** "Formal verification": "the external theorems of Section 1.4" did not include the matching theorem of [30].
  Applied: "The external theorems (Theorems T and $T^+$ of [18] and the matching theorems of [19] and [30]) are used under their
  stated hypotheses."
- **M3 MENOR** Spanish §1.3: "la versión enumerativa" overstated the relation to [10, Theorem 1.1]. Applied: "un análogo enumerativo".
- Editorial, applied: E1 (companion ES gender), E2 ([38] title equal to the companion's), E3 (ν_XΓ ≤ 1−p stated), E5 ("three
  ingredients of the completion"), E6 ("paper" throughout the Spanish; cover-down gloss at its first appearance in the body), E7
  (alternantes; American spelling in the companion), E8 (Corollaries 1.4, 1.6, 1.8, 1.11 named). E4 not applied: "ninguna
  determina a la otra" is the author's wording.

Coverage: VERIFIED — full EN and ES diff against round 4 with the renumbering; all citations by script; Table 2 cell by cell; the
clauses from the definitions; the formal paragraph against FREEZE, mapping notes, logs and companions; claims about [1], [2] against
their texts; Python libraries against the imports of 03_reproducibility; cross-references, terminology, gender and spelling by script.
READ — §§5.1–5.11, §6, Appendices A–B without re-deriving unchanged text. Not verified — Lean builds; online resolution of the
DOIs of [1], [2], [38]; black boxes T/T⁺, [19], [30], the corpus of [10].
