# Audit round 1 — bibliography and internal consistency (independent agent, read-only, 17 Nov 2026)

Verdict: **PASS WITH RESERVATIONS** (no BLOQUEANTE/SERIO; nine MENOR and several EDITORIAL). All 31 references checked (metadata and
DOIs; SOURCE_VERIFIED where read on arXiv/Crossref/publisher); all locators; all internal cross-references; spelling by regex;
notation by full reading. Weaker: Berend (abstract only); numbering in published versions of [1, 4, 7, 15, 20, 25, 31]; [5], [9] read
in local copies.

Findings L1–L9 and C1–C6 and the notation table are reproduced, with the decisions taken, in `FIX_BRIEF_R1.md`. Key facts:
- L1 Simkin is not an author of [21] or [22]. L2 [6] proves the empty-box bound (Thm 1.2) and conjectures box discrepancy.
  L3 [7, Prop. 15] is a ratio bound; the factorization is in its proof. L4 [2, Thms 2.1, 2.8] are existence and nibble, the count is
  carried out by Kwan [4, Thm 3.2]; Luria [3, Thm 3.1] needs exact regularity ("an adaptation of"). L5/L6 Sudoku: Luria [3, Cor. 3.2]
  upper bound; Mahdian–Mahmoodian prove (1/e + o(1))^{n²} [19, Thm 5, Cor 1] (arXiv; the ENDM version is an extended abstract);
  Keevash [31, Thm 2.7] (not 2.8) determines the count asymptotically. L7 [25, Thm 3.5] gives an unspecified ε₀; 1/4 is not from [25].
  L8 [LAT] DOI 10.5281/zenodo.24284129 returns 404; the other five Zenodo DOIs resolve; release latinon-v1.0 responds 200. L9 metadata
  and DOIs (all resolve; [8] DOI 10.19086/da.83253 returns 404, as cited in paper 1); add Brègman, Egorychev, Falikman, Chernoff,
  Hoeffding; Kim–Vu unused; spelling "Bregman" as in paper 1.
- C1 §5.2 "independent coordinates of Section 2" (should be Sections 5.1, 5.6). C2 stage-1 references, "stage-1 target", define Φ_O,
  "n ≡ 1, 3 (mod 6)". C3 |B| ≤ 2Cn^{1−θ} in §6.3 as in §5.4. C4 Generalized, fiber, Nash-Williams. C5 locator style. C6 "rich" (three senses).
- Content queries: A-1, A-3, A-14 NOT-AN-ISSUE; A-4 NOT-AN-ISSUE in the text (MathSciNet not consulted; zbMATH 403);
  A-10, F-4, F-5, F-6, F-7, A-11, A-12, A-13, F-8, F-9, F-10, E-5 STILL-OPEN with the fixes above.
