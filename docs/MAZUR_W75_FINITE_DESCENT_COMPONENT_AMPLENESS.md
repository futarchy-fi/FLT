# Finite descent and the curve component criterion

The finite-surjective ampleness theorem (Stacks 0B5V) is now proved for
schemes proper over a Noetherian ring. The curve component-degree criterion
(0B5Y) and its finite-divisor support consequences are also proved.
These results do not remove `Mazur_statement`: arbitrary-base approximation
and fiber-to-neighborhood ampleness, followed by A7–A8, remain unfinished.

## Finite descent

`GenericIdealSumComparison` proves positivity of the generic comparison rank,
retraction from a nonempty finite sum to one ideal, and generic invertibility
of the coordinatewise ideal-containment map.

`GenericWitnessIdealVanishing` compares the finite sum of an intersection
ideal with the original witness. Reverse comparison and smaller-support
errors give vanishing on the sum. Retraction gives one ideal, and extension
by a smaller-support quotient gives every nonzero ideal on that integral
closed subscheme. There is no assumption that the generic rank is one.

`IdealWitnessSupportInduction` combines this step with the actual geometric
ideal filtration and Noetherian closed-support induction. This is the
specialization of 01YM to eventual positive twist vanishing. Its witness
hypothesis requires all ideal multiples to vanish; the finite-direct-image
application proves that stronger hypothesis using W74's 01YP comparison.
The proof uses extension and quotient closure, never false kernel closure.

`SurjectiveStructureSupport` proves that a dominant quasi-compact morphism
to a reduced scheme has a structure-module direct image of full support.
`FiniteSurjectiveCoherentWitness` then constructs 01YO's coherent witnesses.
For an integral closed immersion Z → X and finite surjective Y → X, it uses
O(Y ×_X Z), pushed along the closed immersion Y ×_X Z → Y. The pushforward
to X also factors through Z. This proves exact support Z and annihilation
by the generic maximal ideal, without choosing a reduced closure upstairs.

`ClosedPointLineSection` proves that lines on a one-point scheme are trivial
and lifts a section through the actual comaximal ideal sequence.
`IdealCohomologyAmpleAnyBase` uses this at closed points to extend the previous
field-only ampleness criterion to compact locally Noetherian schemes.
`FiniteSurjectiveAmpleDescent` assembles these results over a Noetherian ring,
including eventual vanishing for every coherent coefficient and both
implications of finite-surjective ampleness detection.

## Components and fibers

`IrreducibleComponentAmple` proves ampleness detection on reduced irreducible
components, including nonreduced ambient schemes. It uses geometric ideal
filtration and finite direct-image vanishing; no finite-coproduct presentation
of the normalization is needed.

`CurveComponentAmpleCriterion` proves 0B5Y for proper schemes of dimension
at most one. Only one-dimensional components have a positive-degree condition.
The zero-dimensional integral components are discrete one-point schemes,
where every line is trivial and ample.

`CurveDivisorAmpleSupport` identifies ampleness of a finite effective Cartier
divisor on a proper pure curve with meeting every irreducible component.
It also proves this equivalence for `RelativeAmple`, the project's predicate
using closed projective presentations of positive powers. For integral curves,
the criterion is nonempty support.

`GeneralizedCurveFiberAmple` supplies the smooth geometrically integral curve
case, the component criterion for an actual `ClassifiedFiberCore`, and the
criterion for every supplied polygon pinching cocone. The smooth nonempty
support corollary explicitly assumes geometric integrality; it does not claim
that the classified core's smooth alternative alone has supplied that fact.

## Remaining boundary

L1: descend a proper finitely presented family and its invertible sheaf to a
finite-type integer model; descend the relevant fiber presentation as well.
This finitely presented case is the first target; full 0D2S assumes only
properness and uses an inverse system of proper models with affine transition
maps, rather than one model whose base change is the given scheme.
Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` in
`AffineTransitionLimit` factors maps into an already fixed target. That
result alone does not construct the required family or line-bundle model.

L2: prove the Noetherian fiber-to-neighborhood theorem (0D2N), then use L1
and base change to obtain the arbitrary-base statement 0D2S. Existing
`relativeAmple_of_base_neighborhoods` glues neighborhoods already supplied;
it does not construct a neighborhood from an ample geometric fiber.

A7–A8 remain downstream: compatible cyclic-level isomorphisms, their
quotient/presheaf coherence, and the exact-order point-to-subgroup bridge.
The parallel point-extension and Jacobian workers' assignments are untouched.

## Rechecking

Each listed module is under 240 lines. Build in the foreground with
`LEAN_NUM_THREADS=2 lake build FLT.Mazur.<Module>` and lint that module alone
with `LEAN_NUM_THREADS=2 lake exe runLinter FLT.Mazur.<Module>`.
The untracked W75 handoff records checked-at evidence, declaration axiom
allowlists, source hashes, the local commit, and the post-merge root build.
