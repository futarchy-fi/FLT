# Genuine line transition data over a finite integer model

This increment advances L1 / 0D2S. It does not remove `Mazur_statement`.

## Section coordinates

`finiteIntersectionSectionEquiv` identifies ambient sections on an actual
finite intersection with the coordinate ring already used by the scheme
approximation construction. Naturality identifies restriction maps, and
`finiteIntersectionAmbientAlgebra_scalar` identifies its base scalars with
restrictions of the given structural map's global sections.

## Actual line trivializations

`lineTrivializationCoordinates` takes a genuine sheaf trivialization to
linear coordinates on every ambient subopen. Forward and inverse coordinates
commute with restriction. `linearCoordinateRatio` constructs a unit from
two such coordinates, with inverse and multiplication equations proved.

`lineTrivializationCocycle` constructs the ambient cocycle from these units.
`lineTrivializationCocycleIso` glues the original local trivializations to
identify the cocycle sheaf with the original sheaf. No global generators
or transition equations are required as additional assumptions.

## Simultaneous finite descent

Ordered pairs of chart labels in a nonempty finite intersection index the
transition units; ordered triples index their multiplication equations.
`finiteIntersectionCocycleUnit` transports the genuine cocycle into the
actual coordinate diagram, with restriction compatibility.

`exists_finite_intersection_cocycle_model` applies finite diagram unit
descent to the fixed presentation models. Its enlarged coefficient stage
retains all diagram identities, open immersions and union pullbacks, plus
units, tensor recovery, restriction compatibility and multiplication laws.
It does not infer equalities from injectivity of a recovery map.

`exists_finite_line_cocycle_model` combines compactness, the finite affine
trivializing cover, genuine cocycle recovery and simultaneous descent.
Local finite presentation is used for this intermediate construction;
it has not been added to the proper-only approximation target.

## Next mathematical boundary

The units live in the model coordinate rings. They still need to be
transported to sections on actual overlaps of the glued model scheme,
assembled into a model cocycle and invertible sheaf, and identified with
the original sheaf after base change. Recovery of the cocycle sheaf on the
original scheme does not itself prove this model pullback statement.

`IntersectionGluingCharts` identifies union-label charts with the actual
pairwise overlaps in the colimit. This supplies the first geometric bridge
for constructing that model cocycle.

After sheaf descent, descend properness and fiber data; prove proper-only
approximation without adding local finite presentation; descend ample
fiber presentations and prove Noetherian L2 / 0D2N; then address A7–A8.
The parallel local arithmetic and Picard/Jacobian lanes are unchanged.
