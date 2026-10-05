# Separated coefficient models with line-sheaf recovery

`exists_finite_separated_line_sheaf_descent` strengthens the finite line-sheaf
construction with separatedness of the descended structural morphism.
Its inputs remain a compact separated scheme `X`, a locally finitely
presented `p : X ⟶ Spec A`, a locally free rank-one sheaf `L`, and a finite
set of coefficients to retain.

It constructs a finite-type integer subalgebra `S ⊆ A`, a scheme `Y`, a
separated morphism `q : Y ⟶ Spec S`, a rank-one sheaf `M`, and `f : X ⟶ Y`.
The square with `p` and `Spec A ⟶ Spec S` is cartesian, and the actual
pullback of `M` along this same `f` is isomorphic to `L`.

## Construction

- `IntersectionModelClosedProducts` applies simultaneous tensor-product
  closedness descent to every pair of nonempty chart sets. It normalizes
  coefficient instances to one per diagram object, even when an object
  occurs in multiple positions.
- `FiniteIntersectionClosedModel` transports identities, compositions,
  coordinate recovery, open immersions, and union pullbacks through the
  common enlargement, retaining closed overlap products.
- `IntegerModelClosedProductTransport` proves that closedness of the actual
  overlap product persists under any later coefficient enlargement. The
  proof uses the compatible tensor presentation and its cartesian transition.
- `FiniteIntersectionClosedCocycleModel` descends transition units and
  multiplicative equations without losing the closed product maps.
- `AffineIntersectionSeparated` identifies union-label overlaps with actual
  intersections in the colimit and applies the closed-diagonal criterion.
  Separatedness transfers to the explicit glue-data structural morphism.
- `FiniteSeparatedLineSheafDescent` applies that result to a finite affine
  trivializing cover and carries the cartesian square and sheaf recovery
  through the same construction.

No faithful-flatness or injectivity of coefficient recovery is assumed.

## Remaining foundation

General universal closedness must still descend along the coefficient
inverse system. The affine properness theorem only descends a proper map
between affine spectra; restricting a proper scheme to an affine source
chart does not in general preserve properness. It cannot complete this step.

A suitable next theorem must start with a finite-presentation model over a
coefficient stage whose pullback to `A` is proper, and produce a larger
finite coefficient stage where that same model's base change is universally
closed (retaining the cartesian comparison). The coefficient inverse-system
construction and this eventual-property theorem are not supplied here.

Fiber conditions, an ample fiber presentation, Noetherian L2 / 0D2N, and
approximation for the proper-only 0D2S target remain open. The local
finite-presentation assumption above must not be inserted into that target.
A7–A8 coherence and rational-point/subgroup work follow afterward.
These theorems do not remove `Mazur_statement` from the Fermat endpoint.
