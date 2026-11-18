# Fix brief — round 1 audit findings

You are applying audit fixes to ONE part of the manuscript. Edit only your part file
`C:\nw\color-stats-paper\editorial\parts\edited_<K>.md` (Write/Edit it in place). Do not touch any other file; no git.
Return a short list of what you changed (finding ID → done / not applicable / adapted, with the reason) as your final message.

## How the parts work
- Parts use **citation keys** (e.g. `[Kwa20]`, `[CDR3, Lemma B.1]`), not numbers. The audit reports cite numbers: convert
  them with `C:\nw\color-stats-paper\editorial\citation_map.json` (key → number).
- Parts use **British spelling** (colour, labelled, normalised, neighbour). The build converts to American. New text may be written
  in either spelling; keep existing words as they are.
- Math is LaTeX in `$...$` and `$$...$$`. Keep every existing equation tag.
- Never change a statement, hypothesis, constant or proof step except as a listed finding requires. If a fix in the report does not
  fit the current text exactly, adapt it minimally and say so.

## Audit reports (read the parts relevant to your sections)
`C:\nw\color-stats-paper\02_validation\audit\R1_S1-4_appendices.md`, `R1_S5.1-5.7.md`, `R1_S5.8-5.11.md`, `R1_S6-8_latin.md`,
and the literature/consistency report summarised below (L*, C*).

## Global decisions (resolve conflicts between auditors)
- Remark 7.2 and the matching sentence in §1.3: replace "four equal classes" by "four classes with proportions
  $(0.47,0.289,0.121,0.121)$" (these are the admissible proportions of the numerical check; the numbers $0.634$ and $0.501$ stay),
  and add the short proof that equality is impossible for $k\ge4$ (round-1 §§1–4 M1 text, first sentence).
- Sudoku: Keevash's count is **[Kee19, Thm 2.7]** (not 2.8). Mahdian and Mahmoodian **prove** the fraction
  $(1/e+o(1))^{n^2}$ ([MM17, Theorem 5 and Corollary 1]). Luria's Sudoku result is an upper bound [Lur17, Cor. 3.2].
- Kwan–Sah–Sawhney / Kwan–Pham sentence: use L1 below (no Simkin).
- Spelling of the classical theorem: **Bregman** (as in the Latinon paper), not Brégman.
- New references (part F adds the entries; parts A and B cite them at first use): `[Bre73]` L. M. Brègman, Some properties of
  nonnegative matrices and their permanents, Dokl. Akad. Nauk SSSR 211 (1973), 27–30; `[Ego81]` G. P. Egorychev, The solution of van der
  Waerden's problem for permanents, Adv. Math. 42 (1981), 299–305; `[Fal81]` D. I. Falikman, Proof of the van der Waerden conjecture
  regarding the permanent of a doubly stochastic matrix, Mat. Zametki 29 (1981), 931–938; `[Che52]` H. Chernoff, A measure of asymptotic
  efficiency for tests of a hypothesis based on the sum of observations, Ann. Math. Statist. 23 (1952), 493–507, doi:10.1214/aoms/1177729330;
  `[Hoe63]` W. Hoeffding, Probability inequalities for sums of bounded random variables, J. Amer. Statist. Assoc. 58 (1963), 13–30,
  doi:10.1080/01621459.1963.10500830. Remove Kim–Vu from the list of classical results (unused).
- Notation renamings (apply only inside your part, consistently):
  - right inverses $\Phi$, $\tilde\Phi$, $\Phi_1$ of Lemmas 5.7, 5.8, 5.13, 5.16, 5.19, 6.3, 6.4 → $\Psi$, $\tilde\Psi$, $\Psi_1$ (the rate $\Phi(t)$, $\Phi_G$, $\Phi_O$ keep $\Phi$);
  - in Lemmas 5.19 and 5.21: operator $T\to\mathcal T$, kernel $K_2\to\Pi_2$, error operator $E\to\mathcal E$, Neumann index $s\to j$, polytope $K\to\mathcal K$ (also in Part (b)), minimal entry $s\to x_{\min}$;
  - matching tuple $M=(M_\tau)$ in §6.3 → $\mathcal N=(\mathcal N_\tau)$ (the outline keeps $M$);
  - list-size threshold $s$ of §5.4 and §6.3 (and "$2s$", "$s/4$") → $s_0$; the Latin leftover set $S_r$ → $Z_r$;
  - hinge edge set $J$ (Appendix A H4, §5.9 H3/H4, §6.5) → $E_h$ ($J$ keeps the number of free coordinates);
  - partial Steiner triple system $Q$ of §1.3 and Corollary 1.11 → $\mathcal Q$ ($L_{\mathcal Q}$, $t(\mathcal Q)$, $\deg_{\mathcal Q}$, $|\mathcal Q|$);
  - the bad set $B$ of §5.4/§6.3 → $\mathrm{Bad}$; in §4.2 Step 6 write the number of blocks as $b_n=n(n-1)/6$;
  - Lemma 6.6 indices $a,b,e$ → $x,y,z$; Lemma 6.3 total $T$ → $W_\Sigma$; Lemma 6.5 quotient map $\chi$ → $\psi$; $B_{jl}$ → $A'_{jl}$.
  Do not rename anything else.

## Literature/consistency findings (L*, C*) — by part
- **A (§§1–3):** L1 "Kwan, Sah and Sawhney [KSS22] study large deviations of the number of intercalates in a random Latin square, and Kwan
  and Pham [KP26] study lower tails at criticality, including Steiner triple systems without Pasch configurations."; L2 "Linial and Luria
  [LL16] show that in a random Latin square every box containing no entry has volume $O(n^2\log^2 n)$ and conjecture a discrepancy bound on
  all boxes."; L3 "the proof of [KS18, Proposition 15] uses this"; L4 single-density case: "…the upper bound from an adaptation of
  Luria's bound [Lur17, Thm 3.1] … and the lower bound from Keevash's method, the nibble [Kee18a, Thm 2.8] followed by the completion
  [Kee18a, Thm 2.1], as carried out by Kwan [Kwa20, Thm 3.2]. For $G=K_n-L_{\mathcal Q}$ with $\mathcal Q$ a quasirandom partial system,
  both bounds are due to Kwan [Kwa20, Thms 3.1 and 3.2], with polynomial error."; L5 Methods: "the Sudoku bounds of Luria [Lur17, Cor. 3.2]
  and of Mahdian and Mahmoodian [MM17], and Keevash's count of Sudoku squares [Kee19, Thm 2.7]"; C4 "fibre" → "fiber"; A-12, A-13 (texts in
  the §§1–4 report, M6 and A-13); A-7 add the remark on admissible three-class partitions; A-9; A-11 ($\mathcal Q$).
- **B (§4–5.4):** L3 in the title of Lemma 4.1: "(factorization; cf. the proof of [KS18, Proposition 15])"; L7 "Take
  $\varepsilon_G\in(0,\min\{\varepsilon_0,1/4\})$, where $\varepsilon_0$ is given by [GJKKL, Thm 3.5] for uniformity 3 and conflict
  parameter 2."; C1 §5.2 "independent coordinates of Sections 5.1 and 5.6" (not "of Section 2"); C2 stage 1 "(Section 5.3)"; cite [Che52]
  at the first Chernoff bound (proof of Lemma 5.1) and [Hoe63] at Hoeffding's inequality (G4 in §5.3); "the coloring statistics" etc. unchanged.
- **D (§5.8–5.9):** C2 "stage-1 target", define $\Phi_O$ ("where $\Phi_O$ is $\Phi$ computed with $N^O_\tau$"), "$n\equiv1,3\pmod 6$" for "admissible $n$";
  C4 "Nash–Williams" → "Nash-Williams" in the text (not in the title of [TD1]); C5 use "Theorem", "Proposition", "Lemma", "Corollary",
  "Appendix B.4" style consistently with the rest of your part.
- **F (§6–end, references):** L6 Remark 7.3 from "Yet": "Yet Mahdian and Mahmoodian prove that the fraction of Latin squares that are Sudoku
  squares is $(1/e+o(1))^{n^2}$ [MM17, Theorem 5 and Corollary 1]. So the $o(n^2)$ term in Theorem 1.1 cannot be uniform in the number of
  classes. Fixing about $n^2$ outline entries exactly costs $\Theta(n^2)$ in total. Luria [Lur17, Cor. 3.2] and Berend [Ber18] bound the
  number of Sudoku squares from above, and Keevash [Kee19, Thm 2.7] determines it asymptotically."; L8 [LAT]: "Preprint 1.0, 16 November 2026,
  <https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/latinon-v1.0>; DOI 10.5281/zenodo.24284129 (reserved)."; L9 metadata:
  [LL13] 43(4), doi:10.1002/rsa.20487; [Kee18a] 20(4), doi:10.4171/JEMS/779; [Kwa20] Proc. Lond. Math. Soc. (3) 121(6) (2020), 1468–1495,
  doi:10.1112/plms.12373; [LL16] Discrete Analysis 2016:11, doi:10.19086/da.845; [KS18] 52(2), doi:10.1002/rsa.20742; [GHHS] Discrete
  Analysis 2023:8, 66 pp., doi:10.19086/da.83253 (as in the Latinon paper); [GGS] J. Combin. Des. 34(1) (2026), 5–14, doi:10.1002/jcd.22004;
  [CDR99] doi:10.37236/1457; [EGJ20] Combin. Probab. Comput. 29(6) (2020), doi:10.1017/S0963548320000280, arXiv:1907.09946; [Sim23] Adv. Math.
  427 (2023), 109127, doi:10.1016/j.aim.2023.109127; [MM17] add "Electron. Notes Discrete Math. 49 (2015), 747–755, doi:10.1016/j.endm.2015.06.101"
  besides the arXiv id; [FK20] doi:10.1017/fms.2020.29; [KSS22] Bull. Lond. Math. Soc. 54(4) (2022), 1420–1438, doi:10.1112/blms.12638;
  [FJS20] Combinatorica 40(3) (2020), 315–344, doi:10.1007/s00493-019-3970-y; [DDK25] Electron. J. Combin. 33(2) (2026), #P2.20,
  doi:10.37236/14339; [GJKKL] J. Lond. Math. Soc. (2) 109(5) (2024), e12899, doi:10.1112/jlms.12899; [Fre75] doi:10.1214/aop/1176996452;
  [Ber18] Discrete Math. 341(11) (2018), 3241–3248, doi:10.1016/j.disc.2018.08.005; [Kee19] Building Bridges II, Bolyai Soc. Math. Stud. 28,
  Springer, 2019, 279–315, doi:10.1007/978-3-662-59204-5_9; add the five new entries [Bre73], [Ego81], [Fal81], [Che52], [Hoe63]; drop
  Kim–Vu from the classical list (and the list itself if it becomes empty, replacing it by nothing); C3 Latin "$|\mathrm{Bad}|\le2Cn^{1-\theta}$";
  C4 Appendix B "Generalised" → "Generalized"; C6 "rich" in §6.5 is resolved by the new Lemma 6.5 statement (F-11).
