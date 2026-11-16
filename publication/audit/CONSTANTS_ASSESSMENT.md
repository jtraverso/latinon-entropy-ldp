# Correction constants: adopted and deferred

The directed residual diameter improves from six to five. Transpose the host
and feasible matrix: the residual graph is reversed after exchanging the two
sides. Reversing the four-step row paths of the transpose gives four-step
column paths in the original graph. Same-side paths therefore have length
four and opposite-side paths at most five. The existing no-negative-walk
argument gives a potential of oscillation at most five, centered in [-5/2,5/2].
The margin pairing yields correction cost at most (5/2) times the defect.

Lean compiled CorrectionFive and the canonical entry and all twelve axiom
queries passed, using only propext, Classical.choice and Quot.sound. The
original theorem with coefficient 3 remains available; consumers and numbered
statements keep their original constants. The manuscript records the stronger
consequence after its proof. The LDP constant -2 is unchanged.

Certo 0.40.0 produced an exact rational primal/dual certificate for centering
an interval of width five. Its optimum is 5/2 and independent certificate
replay succeeded. This is optimality of that centering subproblem, not proof
that 5/2 is the sharp constant in the complete correction lemma. Certo is
auxiliary evidence; the Lean proof does not depend on its output.

The capacity threshold 16 and the existing safe pattern-collision constants
are retained. Optimizing them would not change the asymptotic LDP; no claim
of their optimality is made. Further improvements require separate proof and
an updated formal certificate, rather than a silent editorial replacement.
