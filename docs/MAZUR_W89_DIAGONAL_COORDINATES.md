# Compatible diagonal coordinates for coefficient descent

This extends the properness/separatedness item in W88. It does not prove
properness of a descended glued scheme or remove `Mazur_statement`.

## Constructed maps

For fixed finite presentations `P`, `Q`, and `T` over `A`, and a common
coefficient subalgebra `A₀`, the tensor product of the `P` and `Q` models
recovers `B ⊗[A] C` via `tensorIntegerModelRecoveryEquiv`.

`tensorIntegerPresentation` is obtained by choosing a finite presentation
of the actual old tensor product and extending scalars with that recovery.
Its coefficient model identifies with the old tensor product. At every
larger coefficient stage, `tensorIntegerPresentationEquivAt` identifies
it with the tensor product of the enlarged `P` and `Q` models.

Given restrictions `f` and `g` into the `T` model, `tensorIntegerModelMap`
is their product map expressed in the compatible presentation.
`tensorIntegerModelMap_recovery` preserves the specified recovery of both
restrictions. `tensorIntegerModelMap_transport` proves that transporting
this map is the product of the two transported restrictions.

## Closedness and geometry

`exists_tensor_integer_model_closedImmersion` descends closedness of one
recovered overlap-product map. `exists_finite_tensor_integer_closedImmersions`
uses W88's finite-family closed-immersion descent to do this at one common
stage for a finite family. The conclusion uses the actual enlarged chart
products and transported restrictions. No faithful-flatness or injectivity
of recovery is assumed.

`affineProductMap_spec` identifies the spectrum of the algebra product map
with the geometric lift into the product of affine charts.
`affineProductMap_isClosedImmersion_of_isPullback` proves closedness when
the overlap is an actual intersection in a separated scheme.

`finiteIntersectionSectionDiagram_product_closedImmersion` applies this to
W87's actual section diagram. Its source is the union-label intersection,
and its two component maps are the original restriction homomorphisms.

`SeparatedOpenCover.of_overlap_pullbacks` assembles separatedness from
closed product maps of specified actual chart overlaps. The pullback
hypotheses identify those overlaps with the chart intersections.

## Remaining integration

Apply simultaneous tensor closedness to all pairs in the fixed section
model diagram. Retain a common coefficient instance for every diagram
object, all transported diagram equations, open immersions, and union
pullbacks. Use `intersection_colimit_isPullback` and
`SeparatedOpenCover.of_overlap_pullbacks` to prove the enlarged glued
structural morphism separated. Carry W87's actual cartesian recovery and
line-sheaf pullback isomorphism through the same enlargement.

This does not descend universal closedness, proper fibers, or ampleness.
General properness still requires inverse-system descent of universal
closedness; proper-only 0D2S also needs approximation without imposing
local finite presentation on its target. After that come ample fiber
presentation, Noetherian L2 / 0D2N, and A7–A8 coherence and point/subgroup work.
