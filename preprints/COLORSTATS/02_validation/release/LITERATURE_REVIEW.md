# Bibliographic gate — scoped review, 14–17 November 2026

Verdict: **PASS_SCOPED_BIBLIOGRAPHIC_REVIEW**.

This records source checks and the positioning they support. It is not an exhaustive proof that no earlier result exists, and it
does not replace a specialist's priority review. No journal-level rating is used as evidence.

## Novelty filter (14 November 2026)

Sources searched: zbMATH Open (public API), arXiv and web search, alphaXiv, and the citations of arXiv:2010.07854 in Semantic Scholar.
MathSciNet was not consulted. The claims filtered were the Latin-square count with a prescribed outline, the Steiner triple system
count with prescribed block types, and the count of bicolored systems for three classes. No source was found that proves any of them.

The filter changed the presentation in three ways.
- The Latin-square count is related to the entropy prediction of Garbe, Hancock, Hladký and Sharifzadeh [GHHS, Section 12.2]. That
  prediction, for order-pattern densities in a neighborhood, is proved in the author's Latinon preprint [LAT]. The manuscript (§1.4)
  states what can be read off [LAT] for outlines (the upper bound, and the lower bound for near outlines), notes that outlines and
  order-pattern densities are related but not nested, and claims as new the lower bound for the exact fiber.
- The factorization identity behind Lemma 4.1 is known for two classes: it is used in the proof of [KS18, Proposition 15]. The
  manuscript cites it as such and claims only the general-class version with its rate.
- For Steiner triple systems, the closest work is existence rather than counting: Gishboliner, Glock and Sgueglia [GGS] prove that
  high-discrepancy systems exist, and Colbourn, Dinitz and Rosa [CDR99] study when bicolorings exist. Keevash [Kee18a] counts all
  systems without types. The manuscript cites all three as context.

Method precedents that a referee will recognize are cited: Simkin's count of n-queens configurations (entropy maximization over a
limit object, then absorption), Bowtell and Keevash, the Sudoku bounds of Luria and of Mahdian and Mahmoodian, and Keevash's count of
Sudoku squares. Active work on statistics of random Latin squares (Kwan, Sah, Sawhney, Pham and others) is cited where it touches the
paper; none of it treats outlines or block types.

## Audit of the bibliography (17 November 2026, two rounds)

An independent agent checked all 36 references in two rounds:
- metadata (volume, issue, pages, DOI) against Crossref for 19 published entries, and 17 arXiv identifiers against arXiv;
- resolution of every DOI and URL (the DOI 10.19086/da.83253 of [GHHS] is published by the journal but not registered at doi.org,
  so the entry also gives the journal URL);
- every locator in the text, read in the arXiv PDFs of [Kee18a], [Lur17], [Kwa20], [MM17], [GHHS] and [GJKKL]:
  - Keevash's Theorem 2.1 is the completion and Theorem 2.8 the nibble; Kwan's Theorems 3.1 and 3.2 give the upper and lower bounds;
    Luria's Theorem 3.1 needs exact regularity, hence "an adaptation of";
  - [GJKKL, Theorem 3.5] gives an unspecified ε₀ "for all k, ℓ ≥ 2", and its hypotheses hold where it is applied;
  - Mahdian and Mahmoodian prove the Sudoku fraction (1/e + o(1))^{n²} in Theorem 5 and Corollary 1 of the arXiv version (the
    ENDM extended abstract could not be read); Keevash determines the Sudoku count in [Kee19, Theorem 2.7]; Luria's bound is
    [Lur17, Corollary 3.2];
  - Linial and Luria [LL16] prove the empty-box bound and conjecture the discrepancy bound on all boxes;
  - Simkin is not an author of [KSS22] or of the Kwan–Pham paper; the attributions were corrected.
- citation order: all 36 entries are cited and numbered by first appearance.
Classical inputs (Bregman, Egorychev, Falikman, Chernoff, Hoeffding, Freedman) were added with their original sources; Kim–Vu was
removed because it is not used.

## Not verified

MathSciNet; the numbering inside the published versions of the JEMS, PLMS, JLMS and Springer papers (the arXiv numbering was checked);
the ENDM version of [MM17]; the full text of Berend's paper on Sudoku squares (cited only for an upper bound stated in its abstract).
