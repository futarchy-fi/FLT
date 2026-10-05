# W82: affine overlap pullback descent

This increment supplies the missing eventual pullback theorem for fixed
presentation models, and combines it with open-immersion and diagram descent.
It does not complete L1 / 0D2S or remove `Mazur_statement`.

## Contracts

`exists_integer_model_pullback` takes four finite presentations over `A`,
a finite-type integer coefficient subalgebra `A₀`, four maps of their
`A₀`-models, and recovery equations identifying those maps with an affine
cartesian square over `A`. It constructs a finite-type enlargement `S`
containing any requested finite set of coefficients such that the four
**transported original model maps** form a cartesian square.

Neither commutativity nor cartesianness is assumed at `A₀`. Recovery need
not be injective, and the coefficient inclusion need not be flat.
`exists_integer_model_finite_pullbacks` gives one such stage for any finite
family, including the empty family. Established pullbacks persist under
further coefficient enlargement by the existing transport theorem.

The construction first descends the recovered square equation. For a
commutative square it forms the canonical tensor comparison. Scalar
extension preserves the canonical tensor pushout; the recovered square's
pullback property makes the extended comparison bijective. Existing
isomorphism descent then makes that same comparison bijective at a finite
coefficient stage. Base-change equivalences identify its square with the
specified transported model arrows.

`exists_finite_affine_atlas_diagram_model` starts with a finite category of
finitely presented affine algebras, open restriction maps, and a finite
family of marked cartesian squares. It constructs the model arrows and
proves identity, composition, recovery, open-immersion, and marked-pullback
laws at one common coefficient stage. Its fixed-model precursor retains
the actual transported arrows.

`finiteIntersectionSchemeDiagram` constructs a diagram from actual open
charts of a scheme: objects are nonempty finite sets of chart labels, and
arrows are reverse inclusions. On a separated scheme, affine charts yield
affine intersection objects. A finite family of labels makes the indexing
category finite. Singleton objects retain the original cover, and unions
of label sets give the actual intersection pullbacks. This construction
does not require a Noetherian hypothesis.

## Module boundaries

| Module | Result |
| --- | --- |
| `AffineSquareTensorComparison` | Canonical tensor comparison; bijectivity iff the square is cartesian |
| `AffinePullbackCorner` | Bijective corner comparisons and transfer of cartesianness |
| `AffineSquareScalarExtension` | Composition and pullbacks under scalar extension |
| `AffineSquareEquivalences` | Pullback invariance under compatible algebra equivalences |
| `ScalarExtensionIsomorphismDescent` | Eventual bijectivity of the given extended map |
| `ScalarExtensionPullbackDescent` | Pullback descent for a commutative coefficient square |
| `IntegerModelSquareComparison` | Recovery and transport as equalities of full algebra maps |
| `CommutativeIntegerModelPullbackDescent` | Pullback descent for a commutative fixed-model square |
| `IntegerModelPullbackDescent` | Pullback descent without an initial square equation |
| `FiniteIntegerModelPullbacks` | A common stage for finitely many recovered squares |
| `IntegerModelAtlasDiagram` | Fixed diagrams retain laws, opens, and marked pullbacks together |
| `FiniteAffineAtlasDiagramDescent` | Construction of the finite algebra diagram model |
| `FiniteAffineIntersectionDiagram` | Actual finite intersection opens, cover, and pullbacks |

Each new Lean module is capped at 240 lines. Checks are targeted foreground
builds, sequential per-module lint, an originating-declaration axiom audit,
and a root `FLT` build after merging main. The untracked W82 handoff records
the checked source hashes, command results, commit IDs, and check time;
this document describes contracts rather than a live validation status.

## Remaining work in order

1. Connect the actual finite intersection scheme diagram to the algebra
   diagram theorem: give its section rings their base-algebra structures,
   construct compatible finite presentations from the geometric hypotheses,
   and identify the restriction maps and pullback squares in affine coordinates.
   Construct the resulting `Scheme.GlueData`, including the transition maps
   and triple-overlap cocycle on the actual pullbacks, and prove recovery of
   the original covered scheme. The diagram theorem alone is not a glued atlas.
2. Descend the line bundle's transition units and glue the family and
   invertible sheaf, with their pullback identifications. Descend properness
   and fiber data. The proper-only form of 0D2S still needs inverse-system
   approximation; do not add a finite-presentation hypothesis to that target.
3. Descend an ample fiber presentation, prove the Noetherian ample
   neighborhood L2 / 0D2N, and transfer it through approximation.
4. A7–A8: compatible level isomorphisms, quotient/presheaf coherence,
   and the exact-order rational-point/subgroup bridge.

The D local-arithmetic and G2 Picard/Jacobian lanes are independent of this work.
