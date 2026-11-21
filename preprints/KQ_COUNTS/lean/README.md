# R50 — finite Lean adapters (K4/K5)

**Source draft, NOT YET BUILT**. The separate R50 project deliberately avoids
editing the already frozen K3/COLORSTATS formalization.

Three proved-by-written-argument statements requiring a Lean kernel build:

* \`TypedClique.R50.recover_eq\`: recover the original packing by filtering a
  completed design on a fixed pair-host J, provided all later blocks use an
  edge outside J.
* \`TypedClique.R50.complete_injective\`: a completion with an explicit left
  inverse is injective.
* \`TypedClique.R50.weighted_lower_bound\`: the finite algebraic bridge from
  good-event mass and an expected matching count to weighted physical packing mass.

These three source declarations **do not prove** the Bernoulli identity,
near-regularity of the token-lift, GJKKL's applicability, the geometric
R39/R48 cover-down, or the KL theorem.

Pinned Lean 4.35.0-rc3 and Mathlib c55e6e786f49471c72fbddbec5415808896aec1e.

To attempt verification:

\`\`\`sh
cd preprints/KQ_COUNTS/lean
lake exe cache get
lake build
\`\`\`

The root module prints axioms for the three results. There are no
\`sorry\` commands or project axioms in the source; this does **not**
substitute for a successful compiler log.

Issue: https://github.com/jtraverso/latinon-entropy-ldp/issues/4.
