# W25: the divisor subscheme and its cyclic operations

The W24 input is `PolygonBoundaryDivisor.ideal`, a product of section kernels.
It has not yet been identified with a group scheme. The missing W25-named
handoff in BRIEF.md is resolved by the present `PREV_MAZUR_W24_DONE.md`.

## Proof design and caps

1. `DisjointClosedCoproduct` (cap 160): a finite coproduct of closed immersions
   with disjoint images is a closed immersion. Prove injectivity and closedness
   using the coproduct open cover, and stalk surjectivity by source locality.
   Its kernel is the infimum of component kernels. Disjoint supports make the
   ideals comaximal on every affine chart, so their product is that kernel.
   `IsClosedImmersion.lift` then gives the actual subscheme isomorphism, with
   the required inclusion formula. The complete prototype is checked before
   promotion; no assumption of a divisor identification is introduced.
2. `PolygonDivisorCoproduct` (cap 180): apply that isomorphism to the marked
   sections, using W24 separatedness and disjointness. Compose with `sigmaSpec`
   to identify the divisor with `Spec (Fin n → K)`, respecting the base map.
   This gives a global finite free presentation, including characteristic
   dividing n. Rank follows from the coordinate-function basis.
3. Cyclic operations (each future leaf cap 240): use the coproduct of the base
   indexed by `ZMod n`, with addition/negation of indices. Establish its
   inclusion in the split smooth group by the actual unit section, then
   transport along the divisor comparison. Multiplication, inverse, cyclic
   divisor equality and base change require explicit commuting diagrams.
   Split further after checked prototypes, before claiming these complete.
4. The support/ampleness comparison and generalized level moduli remain
   separate consumers. Their full designs depend on the existing line-bundle,
   relative curve and moduli APIs; the G1/G2 gate map is not closed by a
   field-valued boundary example.

## Acceptance

Only new Lean modules and sorted `FLT.lean` imports may change. Each module
must build in the foreground with `LEAN_NUM_THREADS=2`, pass an individual
`lake exe runLinter MODULE`, and pass an originating-declaration axiom audit
allowing only `propext`, `Classical.choice`, `Quot.sound`. Prototypes and logs
stay untracked at the root. Local commits only, with the prescribed author.

## Checked next producer

`ConstantCyclicGroup` (cap 200) constructs, over any scheme S, the coproduct
of n copies of the monoidal unit in `Over S`. Multiplication and inverse use
addition and negation in `ZMod n`; the coproduct/product distributivity API
reduces every group law to the corresponding law on the unit and on indices.
Its complete prototype compiled before promotion. This is a scheme group,
not a list of rational points. `ConstantCyclicInclusion` (cap 160) will map
these components by the identity of Gm into `PolygonSplitGroup`, proving
compatibility with operations and a retraction. `PolygonCyclicDivisor`
(cap 240) must then identify this source with the actual all-one divisor.

`ConstantCyclicGenerator` (cap 80) proves the component sections are powers
of the section indexed by 1. The source is the constant group scheme, and
powers are taken in its actual group of sections. `PolygonCyclicDivisorOrbit`
(cap 120) transports this identity to the divisor and rewrites the product
of section kernels. `PolygonCyclicDivisorPullback` (cap 160) must compare the
actual ideal comap with the pulled-back group, using the existing divisor
pullback isomorphism and preservation of finite coproducts.

`PolygonDivisorDegree` (cap 80) consumes the affine presentation to prove
`FCurve.FiniteLocallyFreeDegree`, with Mathlib's `Scheme.Hom.finrank` at every
base point. `ConstantDegree` then transports the result to the actual ideal
comap under arbitrary scheme base change. Its full prototype compiled.

## Remaining obstruction and next proof targets

Checked at 2026-10-03 12:22 UTC by source inspection of
`DivisorLineBundleSheaf`, `DivisorLineBundleRestrict`,
`DivisorLineBundleSum`, `RelativeVeryAmpleLineBundle`,
`RelativeSerreVanishing`, `FCurveContracts`, and Mathlib algebraic geometry.
The actual positive divisor module `FCurve.divisorLineBundle` and its
local rank-one proof already exist; the older C7 text must not be read as
saying they still need construction. What is absent is the comparison from
component support to positivity of the associated line bundle and thence
to a very ample positive tensor power (Stacks 0B5X/0B5Y).

The next target is a proof for the actual module, for example existence of
`m > 0` with `RelativeVeryAmple C.hom
(ModuleLineBundleTensorPullback.tensorPower (FCurve.divisorLineBundle I hI) m)`
for the constructed boundary ideal. No such witness has been constructed in
W25. A general support equivalence needs component restriction/degree and
the curve ampleness theorem, not just the known nonempty intersections.
These are further theory leaves, not a missing argument that can be supplied
as a record field. Before implementation, split their checked prototypes
into modules of at most 240 lines; no aggregate proof-size claim is made.

After this comparison, G1-A1–A3 still need a relative generalized-curve
object with actual smooth group/action and geometric graph condition,
its morphisms and coherent pullback. G1-A4–A7 then need general finite locally
free subgroup data, cyclic Cartier generators with descent, geometric
ampleness, isomorphism classes and the actual pullback presheaf. W25 proves
the boundary example, not those general constructors. The arbitrary-test-
scheme ampleness upgrade also requires the source/descent care documented
in `FCURVE_CONTRACTS` C7; the Noetherian-base theorem alone does not suffice.
The later gate table in `MAZUR_GOAL_LEDGER` remains open. W25 is partial.
