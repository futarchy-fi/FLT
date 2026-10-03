# W28 direct polygon ampleness: D04a refinement

The W27 contracts in `MAZUR_W27_SPLIT.md` remain the targets. Each new Lean
module has a whole-file cap of 240 lines. No statement about polynomial matching
is a substitute for actual sheaf sections or ampleness.

## D04a split

| Leaf | Module | Contract and proof design | Status |
|---|---|---|---|
| D04a.1 | ProjectiveLineEndpointCover | The Laurent open plus zero and infinity covers every P1 point. Compute the polynomial evaluation kernel and complement of D(X), then use the two-chart cover. | Elaborated prototype W28_ENDPOINT_COVER.lean passes. |
| D04a.2 | PolygonNormalizationTorusPullback | Show a component normalization pulls its torus back identically. Exclude endpoints using actual node nonsmoothness, then use the torus open immersion. | Elaborated prototype W28_TORUS_PULLBACK.lean passes. |
| D04a.3 | PolygonDivisorNormalizationPullback | Pull back each closed marked section through the torus square; other component factors become the unit ideal by disjoint support; pullback commutes with the finite product. | Elaborated prototype W28_DIVISOR_PULLBACK.lean passes. |

One-gon self-incidence and the two-gon are retained. There is no n >= 3
assumption in this plan. D04b/c and D05–D10 still require the genuine dual-ideal,
power, section-space and projective embedding comparisons listed in W27.
