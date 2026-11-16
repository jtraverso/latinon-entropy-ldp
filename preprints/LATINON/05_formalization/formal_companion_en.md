# Formal companion: entropy and large deviations for Latin squares

Juan Pablo Traverso Gianini

Preprint 1.0 — 16 November 2026.

Repository: https://github.com/jtraverso/latinon-entropy-ldp.

## 1. Scope and mathematical interface

This companion records how the statements of the manuscript are represented in Lean. It is a guide to the delivered sources and evidence, not a substitute for the written proofs. The model uses three uniform two-coordinate marginals and retains the measure-preserving order map. Its distance has two order terms and a distribution term testing symbol intervals. Relative entropy takes values in the extended nonnegative reals. Converting it to a real number is justified only after a finite-rate hypothesis.

The formal statements are the protected contracts in the audit record. The upper deviation endpoint uses `ENNReal.ofReal t`; this is the nonstrict floor max(t,0) in the manuscript. The lower endpoint requires a nonnegative finite witness cost. Neither endpoint presupposes a law on an auxiliary collection: both concern the pushforward of the actual uniform finite Latin-square law.

## 2. Principal statement correspondence

**Theorem 2.1 / Teorema 2.1**

`LatinonEntropy.closed_uniform_latinon_upper`

Source: `lean/LatinonBridge/LatinonGlobalDeviations.lean`, line 20.

`LatinonEntropy.open_uniform_latinon_lower`

Source: `lean/LatinonBridge/LatinonGlobalDeviations.lean`, line 46.

**Theorem 2.2 / Teorema 2.2**

`LatinonEntropy.finite_rate_standard_pattern_log_count`

Source: `lean/LatinonPatternConjecture.lean`, line 12.

`LatinonEntropy.empty_standard_pattern_fiber_eventually_zero`

Source: `lean/LatinonPatternConjecture.lean`, line 42.

**Theorem 3.1 / Teorema 3.1**

`LatinonEntropy.finite_latin_tensor_lower_bound`

Source: `lean/LatinTensorLowerBound.lean`, line 51.

**Lemma 4.1 / Lema 4.1**

`LatinonEntropy.correction_lemma`

Source: `lean/QuasirandomCorrection.lean`, line 143.

Proposition 2.3 is the written identification with the published GHHS representations and cut-distance definition. Its disintegration and change-of-variables proof is given in the manuscript; it is not advertised as a new Lean declaration. The formal source uses the measure representation, inverse coordinate pushforwards and two order terms. The manuscript notation does not rename any Lean declaration.

**Good rate in Theorem 2.1**

`LatinonEntropy.latinon_rate_lowerSemicontinuous`

Source: `lean/LatinonFullDyadicKL.lean`, line 42.

`LatinonEntropy.latinon_full_cut_compact`

Source: `lean/LatinonBridge/LatinonCompactness.lean`, line 60.

`LatinonEntropy.latinon_rate_sublevels_compact`

Source: `lean/LatinonBridge/LatinonGlobalDeviations.lean`, line 15.

These three properties have their own axiom queries in the source modules. The completed reconstruction report records their three successful outputs separately from the eight selected endpoint queries in `ReviewAxioms.lean`. All eleven reported only the standard foundational axioms. See `preprints/LATINON/02_validation/CLEAN_REBUILD_AUDIT.json`.

The finite tensor theorem quantifies the order threshold before the profile. The correction theorem has no residual-diameter or potential certificate among its hypotheses. Its explicit box constants and linear coefficient 3 are preserved in Lemma 4.1.

The diameter-six argument is also present internally as `LatinonEntropy.ScaledResidualData.diameter_six` in `lean/ResidualDiameter.lean`. Its absence from the hypotheses of `correction_lemma` means it is derived internally, not that it exists only on paper. Review Lemma 4.1 as a written proof separately from checking its correspondence with that source argument.

## 3. Dependency ledger

The core ledger has 23 steps. The following list gives the declaration and dependencies at each step. The current compiled-source correspondence is in `publication/PROOF_LEDGER.json`. Original source-bound certificates retained inside the Lean archive are historical evidence; the completed reconstruction report certifies the delivered selection.

**1. Model and full cut distance.**

`LatinonEntropy.LatinonMeasure`

Ledger dependencies: none.

**2. Deterministic correction.**

`LatinonEntropy.correction_lemma`

Ledger dependencies: none.

**3. Permanents and marginals.**

`LatinonEntropy.permanental_marginal_l1_le`

Ledger dependencies: none.

**4. Latin process and stopping.**

`LatinonEntropy.profileProcessPolicy`

Ledger dependencies: 2, 3.

**5. Defect recurrence.**

`LatinonEntropy.profile_expected_defect_recurrence`

Ledger dependencies: 4.

**6. Gronwall stability.**

`LatinonEntropy.profile_expected_defect_uniform`

Ledger dependencies: 5.

**7. Uniform survival.**

`LatinonEntropy.eventually_uniform_profile_survival`

Ledger dependencies: 6.

**8. Uniform cut closeness.**

`LatinonEntropy.eventually_uniform_profile_closeness`

Ledger dependencies: 7.

**9. Entropy of the full process.**

`LatinonEntropy.profile_history_entropy_lower`

Ledger dependencies: 6, 7.

**10. Tensor lower counting.**

`LatinonEntropy.finite_latin_tensor_lower_bound`

Ledger dependencies: 8, 9.

**11. Tensor-Latinon bridge.**

`LatinonEntropy.finite_latin_grid_metric_ball_lower_bound`

Ledger dependencies: 1, 10.

**12. Partition upper bound.**

`LatinonEntropy.exists_latinon_partition_ball_count_upper`

Ledger dependencies: 1.

**13. Extended KL rate.**

`LatinonEntropy.latinon_rate_eq_iSup_dyadic`

Ledger dependencies: 12.

**14. Fixed center and order.**

`LatinonEntropy.exists_bounded_latinon_profile_approximation`

Ledger dependencies: 11, 13.

**15. Regularization and local entropy.**

`LatinonEntropy.finite_rate_latinon_entropy_count`

Ledger dependencies: 14.

**16. Full-distance compactness.**

`LatinonEntropy.latinon_full_cut_compact`

Ledger dependencies: 1.

**17. Global LDP.**

`LatinonEntropy.closed_uniform_latinon_upper`

Ledger dependencies: 13, 15, 16.

**18. Contraction and observables.**

`LatinonEntropy.latinonContractedRate_attained`

Ledger dependencies: 17.

**19. Densities, continuity and normalization.**

`LatinonEntropy.sum_latinonPatternDensity`

Ledger dependencies: 1.

**20. Finite coordinate bridge.**

`LatinonEntropy.finite_matrix_pattern_embedding_error`

Ledger dependencies: 19.

**21. Binomial normalization.**

`LatinonEntropy.standard_pattern_profile_uniform_error`

Ledger dependencies: 20.

**22. Counting under closed constraints.**

`LatinonEntropy.finite_rate_standard_pattern_entropy_count`

Ledger dependencies: 18, 21.

**23. Logarithmic count and empty fiber.**

`LatinonEntropy.finite_rate_standard_pattern_log_count`

Ledger dependencies: 22, 16.

## 4. Applications and source assemblies

The application assembly is `LatinonSeriesApplications.lean`. It contains the finite CDR definitions and the Wilson pair-footprint argument, then the factorization correspondence, packing replacement, local entropy products and exact type preservation. Its eight original inputs are retained under `lean/evidence/applications`. The core pattern assembly similarly retains its 18 proof inputs under `lean/evidence/proof-inputs`. An input being retained does not assert that it is compiled as an independent module: the assembled modules are the compilation targets.

**A1.** `finite_rate_factorization_entropy_count`

**A2.** `finite_rate_factorization_pattern_log_count`

**A3.** `replaceSteinerPacking_bicoloured`

**A4.** `wilsonLatinBlockTemplate`

**A5.** `card_restrictedRealizations`

**A6.** `wilson_distinguished_latinon_blocks_entropy_count`

**A7.** `wilson_completed_exact_type_count_eq_base`

**A8.** `residual_subset_completed`

The CDR endpoints quantify an already completed base system containing the distinguished packing. They do not discharge the existence of that base from class-size inequalities alone. The final families are actual block sets, not marked copies. The local squares are recovered from fixed row-column pairs, so their product count has no multiplicity loss. Block-type counts refer to color multisets and are equal to the base counts; fixed configurations in the residue are retained, without asserting that the total number of such configurations is unchanged.

## 5. Toolchain, imports and reconstruction

The delivered project pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its manifest pins eight further ecosystem repositories. The configuration declares 309 local module roots, including the canonical entry and the axiom-query module. The canonical entry imports the principal chain through the application assembly. The source manifest records every selected module and hash. This edition makes no claim of compatibility with the earlier 4.35.0-rc3 snapshot.

Extract the source archive from `preprints/LATINON/05_formalization/Latinon_Lean_v1.0.zip`; it contains the project directory `lean/` and its upstream licenses. Install the pinned toolchain, obtain the pinned external packages and their caches, then from the extracted project run `lake build LatinonFormalization` and `lake env lean ReviewAxioms.lean`, sequentially. The first command builds the configured 309-target library. The recorded reconstruction instead compiled one explicit local target at a time. Its source/configuration hashes, 309 object hashes and module logs are retained. No project object was restored; reuse of external caches is disclosed.

All 309 local targets completed successfully on 16 November 2026. The eight endpoint queries and the three good-rate queries contain only `propext`, `Classical.choice` and `Quot.sound`, with no project mathematical axiom or `sorryAx`. The edition verifier checks their retained logs against the archive and frozen source hashes. It does not invoke Lean or rebuild external packages.

## 6. Provenance and review limits

The source freeze identifier is `7b603942c8d078db6c0a5c8729df7012b7786db8`. Its 309 module files and three configuration/toolchain files have the same bytes as in the completed reconstruction. The source archive is unchanged in this edition. `preprints/LATINON/02_validation/v1.0/FREEZE.json` records its SHA-256 and entry hashes. From the repository root, `python scripts/verify_repository.py` checks the package without requiring access to the development repository or its Git objects.

Nine graphon modules originate from Cameron Freer's graphon project at commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`. The retained provenance file lists removed blueprint metadata and compatibility changes. The finite CDR source cut originates from `jtraverso/cdr-palomar-kernel` at commit `5d1e6fe301e5fc01c92f6145aa34fddfe9c2bd10`. The basic definitions are byte-identical; Wilson compatibility edits and the Latin-array representation change are enumerated. This selection does not import the former absorption existence library.

The internal audit follows the CDR Paper III protocol at series commit `d12d980f8c86d8795e9faa0c6bb274ee936c7c8e`. It separates reconstruction, axiom checks, protected statements, targeted written-proof review, bilingual parity, rendered documents and archive integrity. The edition audit is `publication/LATINON_RELEASE_AUDIT.json`. It is an internal preparation check, not independent peer review or an exhaustive priority certification.