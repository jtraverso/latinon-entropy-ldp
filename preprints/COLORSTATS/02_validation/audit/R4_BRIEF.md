# Round 4 — targeted audit of the changes after the round-3 PASS

Scope: only the passages changed after round 3, plus a regression sweep. Read-only. Severity BLOQUEANTE / SERIO / MENOR /
EDITORIAL; PASS = no open finding of MENOR or higher.

Changes to check (English `01_manuscript/color_stats_en.md`; the Spanish edition mirrors them):
1. Abstract rewritten by the author (split into shorter sentences). Check that every claim matches the theorems (1.1, 1.2, 1.5,
   1.6, 1.7, 1.8, Proposition 1.3 and Corollary 1.4 for the 2/3 constant), that P₀ and P are defined as in Section 1.3, that the
   phrase "Unlike earlier large-deviation estimates for neighborhoods of a limit object" is consistent with §1.4 and [12], and that
   no hypothesis is overstated.
2. Last paragraph of §1.1 (index of results): every statement reference correct.
3. After Corollary 1.11: "Corollary 1.11 provides the asymptotic count corresponding to the existence theorem [8, Theorem 1.1],
   under the additional requirement that the leftover graph be typical." Check against [8] as described in §1.4 and Appendix B.
4. Opening of Section 6: "transversal class triple", "nine-point exchanges are replaced by intercalate exchanges", "vertex
   balance" consistent with §§5.2, 6.1–6.6 and Lemma 6.6.
5. Deductive openers "So" replaced by "Hence", "Thus", "Therefore", "Consequently" in §§1.3, 5.3, 5.4, 5.6, 5.8, 5.9, 5.10, 6.3,
   6.5, 7: check that no logical dependency changed.
6. New formalization paragraph (Section 1.7) and the formal companion `05_formalization/formal_companion_en.md`: every claim
   about Lean must be supported by `05_formalization/FREEZE.json`, the logs and `MAPPING_NOTES.md`; in particular the error of
   the formalized upper bounds (weaker than the written O(n^{3/2})), the hypotheses of Lemma 5.17 in Lean, and the list of what is
   not formalized.
7. Regression sweep: cross-references, citation order, renamings, spelling; parity record `02_validation/PARITY.json`.
