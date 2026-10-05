# Finite intersection coordinates and gluing

This increment connects the two constructions left separate in W82: the
actual intersection schemes and the finite algebra-diagram descent theorem.
It constructs their coordinate models and glue data. It does not complete
L1 / 0D2S or remove `Mazur_statement` from the Fermat endpoint.

## Geometric inputs

Let `p : X → Spec A` be locally of finite presentation, let `X` be separated,
and let `U` be a finite family of affine opens. Nonempty finite sets of chart
labels index the intersections. The model construction does not require
these opens to cover; the recovery isomorphisms require `iSup U = ⊤`.

`AffineBaseSectionAlgebra` constructs the actual base algebra on global
sections from `p` and the canonical sections-of-Spec isomorphism. It proves
linearity of section pullback, the functor laws, and finite presentation
from geometric local finite presentation. `AffineBaseSectionFunctor`
packages this as a functor on schemes over the affine base. The spectrum
identifications retain both the arrows and the structural maps.

`FiniteIntersectionSectionDiagram` applies this to the actual open
intersections. Their finite algebra presentations are derived, not assumed.
`FiniteIntersectionCoordinateSquares` transfers open immersion and union
pullback laws through the natural spectrum identifications.

## Constructed integer model

`exists_finite_intersection_integer_model` supplies a finite-type subalgebra
`S ⊆ A` over the integers, containing any prescribed finite coefficient set,
with presentations, model arrows, identities, compositions, recovery, open
immersions, and every marked union pullback at the same stage.

`exists_finite_intersection_glued_model` packages these arrows as an actual
algebra functor and constructs its scheme gluing over `Spec S`. Its recovery
identifications retain the **full scalar-extended algebra maps**, rather
than only elements of the form `1 ⊗ x`. No injectivity of recovery or
flatness of the coefficient inclusion is assumed.

## Gluing and recovery

`intersectionDiagram_isLocallyDirected` derives the gluing condition from
the marked union pullbacks: equal-image points lift to their union
intersection. Mathlib's locally directed gluing then constructs
`Scheme.GlueData`, including transition maps and the cocycle on actual
triple pullbacks. The algebra structural maps form a cocone and give the
map from the glued scheme to its coefficient base.

`finiteIntersectionSchemeCoconeIsColimit` proves the original covered
scheme is the colimit of its intersections, by gluing morphisms and checking
agreement on the actual pairwise pullbacks. This gives
`finiteIntersectionGluingIso`. The natural spectrum identifications give
`finiteIntersectionCoordinateGluingIso` for the coordinate diagram itself.

`AffineIntersectionScalarExtension` constructs the tensor-extended functor,
preserves its open immersion and union-square laws, and turns compatible
algebra recovery into a natural spectrum isomorphism.
`finiteIntersectionScalarGluingIso` then identifies the gluing of these
scalar-extended coordinates with the original covered scheme.

## Exact remaining boundary

Gluing the extended coordinates has been recovered. The global pullback
identification of that gluing with the base change of the glued `S`-model
is still missing. In particular, the existence of a model gluing plus
objectwise affine pullback squares is not yet a proof of scheme descent.
The next leaf should prove gluing commutes with this base change and retains
the structural maps; `Mathlib.AlgebraicGeometry.RelativeGluing` provides
relevant equifibered-diagram and chart-pullback lemmas.

Then descend transition units and the invertible sheaf with their pullback
identifications, properness, and fiber data. The proper-only 0D2S target
still needs inverse-system approximation. This increment's local finite
presentation assumption is not an added hypothesis on that target.
L2 / 0D2N and A7–A8 remain subsequent work. Parallel lanes D and G2 are
outside this increment.

## Rechecking

Build each of the twelve new modules separately with
`LEAN_NUM_THREADS=2 lake build MODULE`; lint each with
`lake exe runLinter MODULE`. The untracked W83 handoff records exact modules,
commits, source hashes, validation logs, axiom allowlist results, and the
post-merge root build. The source checker reruns the recorded-state checks;
a fresh build or axiom audit is needed after changing the sources.
