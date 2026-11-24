# Formal companion to Counting Steiner designs with prescribed color profiles

Juan Pablo Traverso Gianini

## 1. Reading the two main statements

For Theorem 1.1, import `Reconstructed` and inspect `KqR75.PhysicalCompletion.eventually_designFibre_bilateral` in `R75.lean`. A coloring is a function from the labeled point set into a nonempty finite type. A quota is integer valued. The margin equations compare counts of actual pairs, so a histogram cannot enter the lower bound merely by having the correct total mass. The conclusion gives positivity of the fiber and bounds its logarithm on both sides. The error constant precedes the quantifiers over the order, the coloring and the quota. The companion upper theorem, `KqR75.UpperCounting.eventually_card_designFibre_upper_entropy`, bounds the cardinality directly. This distinction matters when a fiber is empty.

For Corollary 10.1, `KqR75.ProfileLDP.designProfileLDP_probability` in `DesignProfileLDP.lean` takes a sequence of colorings whose proportions tend to positive limits along admissible orders. In the closed-set bound, one tests every real number strictly below the rate at every feasible point in the closed set. For an open set, one tests each feasible point and each positive tolerance. The ratio in both conclusions is the number of designs in the event divided by the number of designs of that order. These exponential inequalities give the logarithmic limits in the manuscript and treat events of zero probability directly. Compactness of the feasible rate sublevels is the third conclusion of the same declaration.

## 2. Following the proof through the source

**Sections 1–2.** The margins in the theorem are defined in `ExactPairMargins.lean`. The three entries of the inverse for the complete graph and its column-sum estimate can be checked in `CompleteJohnson.lean`; restricting and inverting the perturbed matrix leads to `solve_defect` in `HostCorrection.lean`. The second correction is on the fixed-dimensional space of histograms. Its purpose is to prescribe the load on each remaining edge and the totals by type at the same time. See `JointCorrection.lean`.

**Section 3.** The finite-field cell is realized on the actual vertex set in `PhysicalAffineCell.lean`. In particular `pair_covered_once` and `switch_cell` certify the edge covering and the alternative decomposition of one cell. The triangular elimination on color profiles gives an integral correction with bounded coefficients. It is also what permits rounding in the large-deviation lower bound.

**Sections 4–5.** Start with the inequality on one block in `SignedBlock.lean`. Summing that inequality with the weights of the currently available cliques gives the signed contribution to the physical drift. The step estimate is `energy_drift_rate` in `PhysicalDrift.lean`. The stopped argument first controls the fraction of available weight of each type and then the number of choices of that type. The resulting physical count is `eventually_count` in `PhysicalHorizonCounts.lean`.

**Sections 6–7.** In `PhysicalCover.lean`, `eventually_cover_physical` completes the covering of the leftover using the reserve. The graph case of Delcourt and Postle enters through `OmniBridge.lean`. The bridge derives placement from the imported `RefinedAbsorption.Original2024.theorem_1_7_two_le`. In `CorrectedCompletion.lean`, `corrected_completion` uses the reserved cells on a completed covering. At this point the histogram defect has zero pair margins and can be switched away.

**Sections 8–9.** In `PrefixRecovery.lean`, `recover_picked` identifies the chosen cliques inside the final design, and `order_fibre_card` controls how many ordered histories are thereby counted. The upper bound has a separate route through `UpperWeightedReveal.lean`, `UpperExceptionalWeight.lean` and `UpperEntropyRate.lean`. It applies even if a particular type has weight zero.

**Section 10.** In `QuotaRounding.lean`, `KqR75.SlotPairMargins.round_quotas` preserves the integer pair margins while approximating a real target. The comparison of finite type laws with the limiting law is in `ProfileTypeLaw.lean`. The count, rate and topological arguments appear in `DesignProfileCounts.lean`, `DesignProfileRates.lean` and `ProfileLDPPrinciple.lean`. The final assembly in `DesignProfileLDP.lean` uses ordered pair margins. The declaration `orderedMargins_eq_iff` supplies the equivalence needed to read them as the pair-type constraints in (10.1).

**Named intermediate lemmas.** Lemma 2.1 uses §2's incidence inverse (`HostCorrection.solve_defect`); Lemma 3.1 uses `SlotPairMargins.affine_spans_kernel` and the physical cell switch. Lemma 6.1 uses `OmniBridge.exists_omni`, `eventually_absorption_budget` and `physical_completion`. Lemma 7.1 combines the good-prefix estimates with `corrected_completion`. The two-color diagram and the elementary Pinsker deduction in §10.1 illustrate Corollary 10.1 in the written exposition.

## 3. Source and verification

The freeze contains 162 project modules, the Lake lockfile, and the verification programs and logs. Import `Reconstructed` using Lean 4.35.0. Earlier incremental compilation records accompany the enumeration and LDP source certificates.

The kernel loaded 59 external imports from pinned, compiled dependencies and replayed 1,997 project declarations. The catalogue printed 1,750 theorem records with their proof terms, representing 1,741 distinct names, including private and generated lemmas. Every axiom set is contained in `propext`, `Classical.choice` and `Quot.sound`.

In `steiner-profiles-lean.zip`, look up a module and name in `verification/THEOREMS.txt` for its signature and axioms or `verification/PROOFS.txt` for its proof. The archive is the distribution copy of the full proof catalogue. Its checksum is listed in the accompanying `SHA256SUMS`. To repeat the checks, unpack the archive and run from `lean`, specifying a fresh output directory.

```
lake build
lake env python ../verification/recheck.py ../recheck-output
```
