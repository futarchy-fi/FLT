# W30: canonical dual pullback and polygon line invertibility

Every new module has a whole-file cap of 240 lines. The original W29 square
is proved for the original chosen comparisons; no replacement morphism or
invertibility hypothesis was introduced.

| Leaf | Module | Checked proof design | Lines/cap |
|---|---|---|---:|
| D04b.4d.3b.i–ii | ModuleTensorPullbackRestriction | Transpose the tensor comparison along the chosen adjunction, test pure unit sections, prove composition and open-immersion compatibility, then paste the five factors of the restriction square. | 176/240 |
| D04b.4d.3b.iii / D04b.4d.3c | ModuleSheafDualPullbackRestrict | Restrict the actual evaluation, use the tensor square and structure-module coherence, and cancel evaluation by currying. Apply the existing trivial-module result on a rank-one cover and detect invertibility globally. | 169/240 |
| D04b.4e.2 | PolygonDivisorLinePullback | Apply rank-one invertibility to the Cartier ideal in the existing canonical polygon comparison. Retain the actual evaluation and canonical-section identities. | 81/240 |

All three designs were elaborated in untracked prototypes before promotion.
The tensor component proofs needed explicit module arguments to avoid costly
inference through expanded adjunctions. The final dual restriction proof uses
a scoped recursion-depth setting for nested scalar transports.

Checked 2026-10-03 15:49 UTC: all three modules passed individual foreground
builds and sequential individual lints with `LEAN_NUM_THREADS=2`. The originating
module audit checks all 21 declarations, including generated declarations, and
allows only `propext`, `Classical.choice`, and `Quot.sound`.
Evidence: untracked `GOAL_MAZUR_W30_<Module>_build.txt`, corresponding `_lint.txt`,
and `GOAL_MAZUR_W30_ALL_AXIOMS.txt`.

`W30_CONSUMER_CONTRACT.lean` proves the exact square whose types alone were
checked in W29. It also constructs the positive isomorphism for the one-gon
and independently for indices zero and one of the two-gon. Its validation log
is `GOAL_MAZUR_W30_CONSUMER_CONTRACT.txt`.

D04b.4 is now complete. D04b.5/D04c.2 still require affine-coordinate,
transition, tensor-power, and intrinsic common-node-fiber compatibility.
D05–D10 retain the genuine H0/polynomial, normalization-map, generation,
projective-map and closed-immersion contracts in `MAZUR_W28_SPLIT.md` and
`MAZUR_W27_SPLIT.md`. No ampleness or Mazur axiom removal is claimed.

## Affine coordinates and tensor-power transport

The next three leaves were split and elaborated before promotion:

| Leaf | Module | Checked proof design | Lines/cap |
|---|---|---|---:|
| D04b.5a | DivisorLinePullback | Combine canonical rank-one dual pullback with the actual ideal comparison; its existing inclusion identity gives section compatibility. Open immersions discharge the ideal-isomorphism instance. | 79/240 |
| D04b.5b | ProjectiveLineMarkedPullbackCoordinates | Apply the positive comparison to each marked ideal power on the two open charts. Compose the resulting section equivalence with the existing affine dual-generator coordinate; evaluate the canonical section. | 70/240 |
| D04c.2a | PolygonDivisorLinePowerPullback | Transport the proved component line isomorphism through `divisorLineBundlePowerIso` and pullback/tensor-power comparisons. Compose with the marked chart isomorphisms and their section equivalences. | 93/240 |

The six modules contain 668 lines. Checked 2026-10-03 16:01 UTC: all passed
individual foreground builds and sequential individual lints. All 60 originating
declarations pass the axiom audit with only the three permitted logical axioms.
The consumer contract additionally constructs both affine-chart power isomorphisms
for the one-gon and each of the two-gon indices, for arbitrary multiplicity.

These are actual isomorphisms and coordinates, but not yet the matching theorem.
The marked-chart canonical-section identity is proved. Compatibility of the
polygon tensor-power isomorphism with the powered canonical section and the
intrinsic common-node trivializations is still unproved.

## First remaining assertion

`W30_TRANSITION_CONTRACT.lean` defines left and right polynomials by applying
`chartSectionsCoordinate` to the pullback of an arbitrary global section,
represented as a genuine module morphism `𝒪_P1 ⟶ O(m[a])`. It type-checks the
following equality, but does not prove it:

```text
invert (toLaurent (rightPolynomial s))
  = (transition a)^m * toLaurent (leftPolynomial s)
```

The transition is the existing Laurent unit `(-a⁻¹) T⁻¹`. The same contract
proves the canonical-section specialization, confirming the sign, reciprocal
coordinate and multiplicity. This specialization is not sufficient for an
arbitrary section.

The missing comparison is compatibility of the two actual chart section
coordinates on the Laurent overlap. `dual_transition` acts on one common
principal-ideal functional; the new chart coordinates arise from separate
pullbacks, ideal isomorphisms and global-section identifications. Identifying
those two transported functionals is still required. Tensor and dual open
coherence are now available, but no full overlap-coordinate proof was elaborated.

Proposed remaining split (not yet checked proof designs; each cap 240):

1. D04b.5c.1: identify the two pulled-back chart duals on the common Laurent
   scheme, including the chosen ideal comparisons and coefficient-ring maps.
2. D04b.5c.2: apply `dual_transition` to that common functional to prove the
   displayed equality for arbitrary global sections.
3. D04c.2b: preserve the powered canonical section and identify the two branch
   values in the intrinsic node fiber, including self-incidence and both
   two-gon nodes; derive the predecessor-oriented weights.

D05a/b/c still need the genuine P1 H0/polynomial equivalence, the tensorized
normalization sequence with its maps, and identification of polygon H0 with
the weighted matching kernel. D06–D10, generalized-curve/moduli/coarse-cusp
producers, and removal of `Mazur_statement` remain unproved.
