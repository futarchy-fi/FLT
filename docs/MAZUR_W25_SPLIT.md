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
