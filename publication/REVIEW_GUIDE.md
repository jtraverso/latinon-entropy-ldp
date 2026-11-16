# Final audit guide — preprint 1.0

Read the [English manuscript](../preprints/LATINON/01_manuscript/latinon_en.pdf)
and [companion](../preprints/LATINON/05_formalization/formal_companion_en.pdf).
The [edition audit](LATINON_RELEASE_AUDIT.json) records internal preparation;
independent mathematical review remains separate.

1. **Model.** Proposition 2.3 and (2.9)–(2.10): compare GHHS Definitions 3.5,
   3.16, 4.1 and 4.3, inverse coordinate transport and both order terms.
   The proposition is a written identification, not a new Lean declaration.
   Our entropy is minus KL; do not identify its sign with the positive
   display in GHHS §12.2.
2. **Correction.** Lemma 4.1, (4.1)–(4.6): witness A/d, residual expansion,
   repeated arcs, diameter six, potentials and coefficient 3. Source:
   `QuasirandomCorrection.lean` and `ResidualDiameter.lean` inside the ZIP.
   The diameter and potential are derived, not caller hypotheses. The unnumbered
   refinement and `CorrectionFive.lean` improve diameter six to five and the
   coefficient 3 to 5/2 under the same hypotheses.
3. **Lower count.** Theorem 3.1 and §§5–6: weighted Gibbs (5.0), capped
   permanent, the finite size condition for recentring, predictable stopping,
   first-failure estimate (6.4'), active/inactive split (6.4c), Gronwall,
   entropy accounting, tail and cutoff boundary row.
4. **Upper count.** Lemma 7.1, (7.3)–(7.3a): independence is that of the two
   auxiliary owner labels. Check mixture entropy, actual block volumes,
   rounding, dyadic KL recovery (8.1)–(8.2) including singular measures, and
   compactness via the explicit GHHS comparison.
5. **LDP and patterns.** Theorems 2.1–2.2 and §§8–9: finite thresholds,
   contraction, radius before order, finite binomial normalization, empty
   fibers and infinite-rate cases. The current `ReviewAxioms.lean` checks all twelve declarations together,
   including the three good-rate properties and the strengthened correction.
6. **Applications.** Corollary 10.1, Lemma 10.2 and Proposition 10.3:
   ordered bijection, supplied completed CDR base, fixed pair footprint,
   injective recovery, product count and exact six-type preservation. This
   is not an unrestricted second-order count of all CDR completions.
7. **Priority.** Consult the [scoped bibliography review](audit/LITERATURE_REVIEW.md).
   Its negative search is not an exhaustive priority certification.

Run the two root verification commands before reviewing a modified package.
The source ZIP, completed reconstruction and all 31 ledger steps are accessible
within this edition. No private Git objects are needed. Report objections by
theorem/equation and, where applicable, by declaration and source line.
