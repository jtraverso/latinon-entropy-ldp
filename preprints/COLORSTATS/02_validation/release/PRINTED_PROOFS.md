# Targeted written-proof review — preprint 1.0

Verdict: **PASS_TARGETED_WRITTEN_REVIEW**, with the scope below.

The Lean formalization covers only the upper bounds and part of the finite algebra, so this review is the main internal check of
the proofs. It was carried out by independent agents working read-only on the edited manuscript, in five rounds, with the severity scale BLOQUEANTE / SERIO /
MENOR / EDITORIAL. PASS means that no finding of MENOR or higher is open.

## Round 1 (five scopes)
§§1–4 and the appendices; §§5.1–5.7; §§5.8–5.11; §§6–8 (Latin squares, remarks, open problems); bibliography and internal
consistency. Each scope ended PASS WITH RESERVATIONS: no BLOQUEANTE, and the SERIO and MENOR findings were repaired in the text.
The repairs that touch a proof are:
- the exclusion count in steps 4–5 of Lemma 5.6 counts both points of a pair, which gives the condition λ ≤ θ₀δ₀/200 (55/3);
- the conditions of Section 5.10 on λ and the bound e_x(w) ≤ 10λd*/(d₀²δ₀);
- the consistency factor φ = 1 + O(1/n) on ν_XX before (5.1), and per class φ_X in Section 5.9;
- Corollary 1.4 with explicit integral t, entries n²/36 + O(n^{3/2});
- Step 5 of Section 4.2 is O(n^{3/2});
- a new Lemma 6.5 (lattice of balanced vectors) replacing an informal argument;
- the degrees D′_τ in the Latin construction and the proof of Corollary 5.3 with the constant C_L;
- the four-class example of Remark 7.2.
The records are `R1_*.md` in `preprints/COLORSTATS/02_validation/audit` and the fix brief `FIX_BRIEF_R1.md`.

## Round 2
All round-1 findings closed, each with a recorded reconstruction (for example the minimum for k ≥ 4, Lemma 4.2 for d ≥ 2, the
integrality in Corollary 1.4, the Latin consistency formula, the norm in Lemma 6.3). New findings: seven MENOR (the statement of
Claim A, the order of the rounding mismatch in Section 5.9, the thresholds on δ′ in Section 5.11, the four-class proportions, a
partial C → C_L renaming, the double use of η, and DOI links broken by a final period) and editorial items. Records: `R2_*.md`.

## Round 3 (closure)
PASS. Every round-2 finding closed, with the threshold arithmetic recomputed (δ′ < 4/1001, 4/1801, 4/2001, 4/9001; δ′ < 3.91·10⁻⁴),
the Hall-type computations of Sections 5.4 and 5.10, the proofs of Lemmas 5.8, 5.16 and 6.5 and the numbers of Remark 7.2 (script
rerun). A regression sweep found no dangling cross-reference, citation out of order or half-applied renaming. Three optional
editorial points were applied afterwards (R3 for |T| ≥ s₀/2, η_T in Appendix A, two spellings). Record: `R3_closure.md`.

## Round 4 (after the author's second editorial round and the formalization section)
Targeted review of the rewritten abstract, the index paragraph of §1.1, the sentence after Corollary 1.11, the opening of §6, the
replaced deductive openers, the new §1.7 and the formal companion. Three MENOR findings: §1.7 overstated the scope and the error of
the formalization (Theorem 1.9(a) also loses O(ηn²); the normalized forms of Theorems 1.5 and 1.7 are not formalized), the sentence
after Corollary 1.11 misdescribed its relation to [CDR III, Theorem 1.1], and the companion still reported an "integer sum" wording that
the manuscript no longer uses. All three were repaired and the closure verified. Records: `R4_BRIEF.md`, `R4_targeted.md`,
`R4_closure.md`.

## Round 5 (the author's third editorial round)
Targeted review of the series framing in the abstract, the new Table 2 (all thirty cells checked against the lemmas), the one-paragraph section "Formal verification" that replaces Section 1.7, two clauses on rescaled availability probabilities (Sections 5.3 and 5.9, verified from the definitions), the renumbered references (every citation checked by position) and the Spanish edition. Three MENOR findings, all of wording: the formal paragraph omitted the typicality loss of Theorem 1.9(a) and named the external theorems imprecisely, and one Spanish sentence overstated the relation of Corollary 1.11 to the completion theorem of CDR III. A separate prose pass looked for generic patterns and calques with the mathematics locked. All applied and the closure verified. Records: `R5_targeted.md`, `R5_style.md`, `R5_closure.md`, `REFERENCE_NUMBERING.md`.

## Lean formalization
The upper bounds of the main theorems and the finite algebra of Sections 5.8–5.10 are formalized (`05_formalization`); the freeze
was built (9030 jobs, 57 project modules, also rebuilt from the archive) and its 89 axiom queries report only the standard axioms.
The formalization complements the written review for those parts; it does not cover the lower bounds.

## Scope and limits
- Read line by line and reconstructed: every new or repaired argument, Lemmas 2.1–6.6 and the assembly of each theorem, as listed
  in the coverage sections of the reports. Read without reconstruction: the Chernoff and Freedman details, the greedy Pasch
  selection, the Latin adaptations of Claims A and B and of Lemma 5.6, and the parts of Lemma 5.19 beyond its norm estimates.
- Black boxes, with hypotheses checked where they are applied: Theorems T and T⁺ (Appendix A), [Ehard–Glock–Joos, Theorem 1.2], [Glock–Joos–Kim–Kühn–Lichev, Theorem 3.5],
  Freedman's inequality, and the inputs from [CDR III] (Lemma B.1, Section 4, Appendix B.4).
- Recorded author decisions: "general $t$-designs" in Open problem 2; the residual r and the hinge set E_h keep their names.
- The reviewing agents are AI systems. Their review is an internal check, not a substitute for refereeing by specialists.
