# Lifting gates after the W45 algebraic leaves

The declarations below specify the delivered scope. Each module is at most
200 lines. `Scratch/LiftsW45/validate.py` runs foreground builds, one-module
linters and named-declaration axiom audits; `check.py` checks the saved receipts
and source hashes. These scripts and their receipts are untracked handoff data.

## R1b2: actual homogeneous components, conditional local generator

`HopfPointFiberHomogeneous` defines each component as the submodule satisfying
W44's actual `pointFiberCoaction` equation. Multiplication lands in the product
degree. Faithful flat descent proves that the identity-degree submodule is the
scalar submodule. For inverse unit degrees, the product is contained in scalars;
equality with scalars is equivalent to that product containing one.

`LocalInvertibleSubmodule` applies local Picard triviality to a unit in the
submodule semiring. It constructs a coordinate and its generator, proves that
this generator spans the original submodule, and uses the inverse submodule
to prove that the generator is an algebra unit. No coordinate isomorphism or
unit generator is an input.

`HopfPointFiberLocalGenerator` combines these results on the actual fibre. Its
**explicit unresolved hypothesis** `hstrong` is that one belongs to the product
of opposite components. It derives module invertibility and constructs the
homogeneous unit, proves the spanning statement, and descends its torsion power
to a unique integral unit. This is a conditional algebraic construction, **not
an unconditional proof that a multiplicative torsor has an invertible component**.
In particular, `hstrong` must not be supplied as a new field of an ordinary model.

The remaining first gate is still to derive the cyclic grading and `hstrong`
from the actual multiplicative coaction. Split it as follows:

1. Construct the coefficient projections from the standard group-algebra
   coalgebra; prove orthogonality and that their sum is the identity.
2. Relate these projections to the actual quotient-fibre coaction, after the
   integral rank-one kernel identification of R1a2 has been constructed.
3. Apply the existing canonical torsor inverse to the universal degree element;
   project its finite tensor expansion to opposite degrees to prove `hstrong`.
4. Apply the W45 local-generator theorem. This step now needs no further local
   Picard or unit-generator argument.

No identification of an arbitrary integral ordinary kernel with mu_p is
assumed or proved here. R1a2 and the general constant quotient model remain
prerequisites; the earlier constant model over ZInvTwo does not supply them.

## R1b3/R1c: evaluation of the actual fibre difference

`HopfPointFiberDifferenceEvaluation` constructs the kernel point from two
fibre points using the inverse of W44's canonical comparison. Its pullback to
the middle algebra is proved equal to antipode followed by convolution, i.e.
the actual Hopf point difference. Evaluating any homogeneous unit gives exactly
the ratio of its two point evaluations; taking a Galois translate gives the
Galois root ratio. No evaluation equality is an input.

The local-generator module applies this result to its constructed generator
and proves its evaluated integral unit equation. Both statements retain the
explicit `hstrong` obligation. They do **not** yet identify the resulting
root-valued class with W42's normalized ordinary Hom class: that requires the
actual rank-one integral/generic identifications and normalization. Unramified
twists and residual coefficient descent of this particular constructed class
remain R1c. The older field Kummer equivalences do not discharge those steps.

## S0a2/S0a3: normalized exponent extraction, with ramification exposed

`NormalizedCharacterExponent` proves that a character factoring through a
surjective prime-field unit character is a power. It constructs an exponent
in 1,...,p-1 and proves that exponent p-1 is equivalent to the trivial character.
The inputs are the actual characters, surjectivity and kernel containment;
there is no supplied weight evaluation.

`OrdinaryInertiaExponent` obtains that kernel containment from an action
condition on the injected line of an actual ordinary filtration. It constructs
the normalized ratio exponent and proves the scalar-inertia criterion even
for nonsplit extensions. Its `haction` is an **unproved arithmetic obligation**
for a general representation, not a replacement for ramification theory.

Still needed: prove this obligation for the intended inertia character,
classify the actual niveau-two representation, identify the non-peu
whole-local cyclotomic branch from its extension class, and prove the
symmetric-power composition-factor comparison in
`LIFTS_NUMERICAL_WEIGHT_CONVENTION.md`. No arbitrary-p Raynaud or Serre-weight
evaluation theorem is claimed or dispatched.

## Lp0/L20/D1a

`QuadraticQuotientLift` extracts the continuous character from an actual
surjective residual rank-one quotient with stable kernel. An involutive
quotient action proves the character quadratic. The fixed sign construction
then gives a continuous rank-one integral `GaloisRep`; its reduction agrees
with the original quotient character and it is trivial on every subgroup
acting trivially on that quotient. This completes the quotient-character
packaging leaf after W44. It does not construct a quotient of every deformation
or the framed local-condition ideal.

`ClosedIdealSimultaneous` constructs the closure of the sum of any family of
ideals. A continuous parameter map kills this ideal exactly when it kills each
member of the family. A solution in a nonzero parameter ring proves the ideal
proper. The constructed quotient classifies all simultaneous solutions.
Identifying arithmetic local conditions with these ideal conditions, and
proving their closure/effectivity, remain separate D1a obligations.

Lp0's integral crystalline weight-two comparison remains untouched. The source
search for crystalline declarations finds only the disclaimer in
`CofinalFlatModels`; that finite-flat reduction criterion is available, but a
crystalline representation comparison API has not been established. A further
leaf must first specify the integral period/representation objects and the
comparison statement; repeating the cofinal model criterion would not prove it.

The global Selmer, modularity, auxiliary-field, finiteness, coefficient-order
and residual-conjugacy gates also remain open. Endpoint axioms are checked in
the handoff receipts; these local algebraic leaves do not remove the lifting
admission.
