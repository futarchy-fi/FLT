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
