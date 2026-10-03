# W31: arbitrary-section Laurent transition

D04b.5c is proved for the exact coordinates of the W30 contract. For every
field K, unit mark a, multiplicity m and actual global section s of O(m[a]),
`ProjectiveLineMarkedSectionTransition.transition` proves

```text
invert (toLaurent (rightPolynomial K a m s))
  = transition(a)^m * toLaurent (leftPolynomial K a m s).
```

The proof uses the canonical section to determine the transition on all
sections. On a rank-one chart, its coordinate times an arbitrary section
equals the arbitrary coordinate times the canonical section. These relations
pull back to the common overlap. Evaluation against a Cartier ideal generator
cancels scalar multiples of the canonical section, because flat pullback
preserves its regular equation. This replaces the proposed direct comparison
of two Laurent ideal functionals without changing either chart coordinate.

| Leaf | Module | Elaborated proof design | Whole-file lines/cap |
|---|---|---|---:|
| D04b.5c.1 | ModuleGlobalSectionPullback | Adjunction-unit semilinear section map; structure-section identity, naturality, composition, and rank-one coordinate relation. | 87/240 |
| D04b.5c.2 | ModuleDualSectionCancellation | Actual tensor evaluation detects scalars; flat affine pullback preserves regularity; a common cancellable section determines transition. | 105/240 |
| D04b.5c.3 | ProjectiveLineMarkedSectionTransition | Apply cancellation to the marked ideal power on the left overlap; use both canonical coordinates and Laurent ring naturality. | 145/240 |

All designs elaborated in untracked prototypes before promotion. Checked at
2026-10-03 16:22 UTC by individual foreground builds and module-only lints
with `LEAN_NUM_THREADS=2`. Each passed. `GOAL_MAZUR_W31_AXIOM_AUDIT.lean`
checks all originating declarations, including generated declarations, against
only `propext`, `Classical.choice`, and `Quot.sound`.
`W31_CONSUMER_CONTRACT.lean` retains the W30 definitions verbatim and proves
the previously unproved arbitrary-section equality. These checks and their
logs remain untracked in the worktree root.

Next split: D05a.1 extracts bounded degree and endpoint coefficients from the
proved transition. D05a.2 must prove the converse gluing and identify actual
H0 with bounded polynomials. D04c.2 still needs powered canonical-section
compatibility and intrinsic common-node fibers with predecessor-oriented
weights. D05b/c and D06-D10 retain the geometric contracts in the W28/W27
splits, including one-gon self-incidence and both two-gon nodes. No ampleness
or removal of the Mazur assumption is claimed here.
