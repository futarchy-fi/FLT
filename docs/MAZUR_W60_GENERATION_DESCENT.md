# W60: faithfully flat descent of generation

This document describes the contracts implemented by the W60 modules.
For current validation, run the individual module builds and linters and the
untracked `W60_CHECK_SOURCE.py`; its output includes a check timestamp.

## Mathematical result

Let `X` be quasi-compact and separated, `S` affine, `f : X → S`,
`g : T → S` flat, surjective and quasi-compact, and `M` a quasi-coherent
module sheaf on `X`. In an actual cartesian square with projections
`p : P → X` and `q : P → T`, the following are equivalent:

- the evaluation of all global sections of `M` is an epimorphism;
- the evaluation of all global sections of the actual pullback `p* M`
  is an epimorphism.

`FpqcGlobalGenerationDescent.globalEvaluation_epi_iff` proves this in the
universe-zero setting of the global base-change API. `X` and `T` need not
be affine. No reducedness, Noetherian, finite-presentation, properness or
line-bundle assumption is imposed on this theorem.

For a line bundle `L`, `LinePowerEvaluationDescent.degree_evaluation_epi_iff`
applies this result in every tensor degree using the actual tensor-power
pullback isomorphism. An ample pullback supplies a generated positive power
downstairs via `exists_positive_evaluation_of_ample`. Generation of one
positive power is **not** asserted to imply ampleness.

## Proof and modules

All modules are capped at 240 lines, including headers.

| Module | Contract |
| --- | --- |
| `AffineModuleEpimorphisms` | Global-section surjectivity detects affine quasi-coherent epimorphisms; surjectivity on affine opens detects arbitrary module epimorphisms |
| `AffineFaithfullyFlatEpimorphisms` | Naturality of the actual affine pullback section isomorphism; faithful-flat scalar-extension reflection |
| `AffinePullbackEpiReflection` | Reflection under affine faithfully flat maps with arbitrary target; actual restriction-comparison naturality |
| `FpqcModuleEpimorphisms` | Reflection under arbitrary fpqc maps, via affine refinement on target charts |
| `GlobalEvaluationSpan` | Infinite free sheaves are quasi-coherent; a spanning global family has epimorphic evaluation when all global sections do |
| `GlobalGenerationTransport` | Global generation transports through actual module isomorphisms and arbitrary pullbacks |
| `FlatGlobalGenerationDescent` | Finite expansion gives spanning upstairs, followed by reflection of the actual evaluation morphism |
| `FpqcGlobalGenerationDescent` | Remove affineness of the covering scheme by affine fpqc refinement |
| `AmpleGlobalGeneration` | The finite common-degree section cover of an ample line bundle gives a finite evaluation epimorphism in positive degree |
| `LinePowerEvaluationDescent` | Degree-by-degree descent and a positive generated power from an ample fpqc pullback |

The reflection proof works with quasi-coherent sheaves on affine charts.
The tilde/global-section adjunction identifies an affine sheaf epimorphism
with a surjective module map. Naturality of the W58 comparison identifies
its pullback with scalar extension. Faithful flatness reflects that
surjectivity. Restricting to target affine opens and refining fpqc covers
then gives the non-affine reflection theorem.

For generation, W59 expands each upstairs section into a finite sum of
pulled-back downstairs sections with base coefficients. These sections
therefore span upstairs. The spanning-family lemma makes their evaluation
epimorphic; W59 evaluation compatibility identifies it with pullback of
the actual downstairs evaluation. Reflection finishes descent.

This proves the D3 generation consumer without constructing a generic
stalk/pullback tensor isomorphism. That separate comparison for arbitrary
module sheaves is not implemented here. The reflection theorem requires
quasi-coherence of both source and target, which is proved for the free
source of evaluation and follows from invertibility for each line power.
It does not assume a field containing a generation or ampleness conclusion.

## Remaining boundary

The next consumer is D4a: the canonical morphism to Proj of the **full**
graded section algebra. The existing finite-coordinate projective-space
maps do not construct it. Its required inputs now include proved descent
of generation in each degree and a generated positive power obtained from
an ample pullback.

Still required, in order:

1. Construct the full graded section algebra, its canonical Proj morphism,
   and compatibility of that morphism with flat base change (D4a–b).
2. Prove the ample/open-immersion criterion and descend that open immersion
   (D4c–d), then assemble relative fpqc ampleness descent (D5/A6).
3. Prove component degree/support, the ample-degree criterion, and the
   arbitrary-base fibre-to-neighborhood theorem for A6.
4. Complete A7–A8: ample cyclic-level quotient/presheaf descent, exact-order
   rational-point finite étale subgroups, ample levels and generator invariance.

These modules do not remove `Mazur_statement` from the FLT endpoint.
The live endpoint check is `lake env lean W60_REMAINING_AXIOMS.lean`.
