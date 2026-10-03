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

D04c.2 still needs powered canonical-section compatibility and intrinsic
common-node fibers with predecessor-oriented weights. The D05a progress and
remaining converse gluing are detailed below. D05b/c and D06-D10 retain the geometric contracts in the W28/W27
splits, including one-gon self-incidence and both two-gon nodes. No ampleness
or removal of the Mazur assumption is claimed here.

## Bounded-polynomial injection and reciprocal construction

The next leaves also elaborated before promotion:

| Leaf | Module | Elaborated proof design | Whole-file lines/cap |
|---|---|---|---:|
| D05a.1 | ProjectiveLineMarkedPolynomialBounds | Extract coefficients of the shifted Laurent polynomial; prove vanishing above m and the unit-weighted reversal law; apply to actual sections. | 126/240 |
| D05a.2a | ModuleGlobalSectionExt | Compare open-immersion pullback with restriction; use the additive sheaf separation axiom on a cover; evaluate structure-module morphisms at one. | 82/240 |
| D05a.2b | ProjectiveLineMarkedSectionInjective | The left polynomial determines the right via Laurent inversion; injective chart coordinates and the cover detect the original section. | 66/240 |
| D05a.3a | ProjectiveLineMarkedPolynomialReciprocal | Reverse the bounded polynomial and shift by m minus its natural degree; prove the Laurent transition and boundedness of its companion. | 69/240 |

The bounded-polynomial map is proved **injective**, not surjective. Its source
is the actual morphism space from the structure module to the divisor line.
`globalSectionHom` and its evaluation identity identify the corresponding
actual section; the linear H0 equivalence has not yet been constructed.

The right chart's polynomial value at zero, divided by its canonical-section
value, equals the top left coefficient. This is a polynomial identity on
actual section coordinates, not yet an identification of intrinsic polygon
node fibers. No node-matching statement follows merely from this calculation.

### First remaining dependency

`W31_GLUE_CONTRACT.lean` constructs the actual left and right chart sections
by the inverse coordinate equivalences and transports them into one common
pullback module. The first unproved assertion is equality of those transported
sections for every bounded left polynomial and its proved reciprocal companion.
The earlier transition theorem applies to sections already global; it does not
supply this converse equality or global existence.

Refine the remaining D05a proof into capped leaves:

1. D05a.3b: prove the converse equality in the actual common pullback module.
   One possible route is to trivialize the pulled-back left Cartier ideal,
   prove regular scalar multiplication injective on its dual, and cancel the
   two local rank-one relations. This is a proposed proof, not an elaborated one.
2. D05a.3c: transport the common-pullback equality to restrictions on the
   intersection of the two chart images and apply sheaf gluing. The exact
   `Function.Surjective boundedPolynomial` target is checked in the contract.
3. D05a.4: package bijectivity linearly through actual H0 and prove both endpoint
   maps. D04c.2 must separately identify common node fibers and power-section
   compatibility before using those endpoints for polygon matching.

D05b/c and D06-D10 are unchanged and unproved. In particular, the one-gon
self-incidence and two distinct two-gon nodes must remain explicit in the
normalization maps and closed-immersion charts.

## Final validation

Checked at 2026-10-03 16:39 UTC: all seven individual foreground module builds
and sequential module-only lints passed, using `LEAN_NUM_THREADS=2`. The final
logs have no warnings. The modules contain **680 new Lean lines**, each below
240 lines. The originating-declaration audit checked **69 declarations**,
including generated declarations, with only `propext`, `Classical.choice`,
and `Quot.sound` allowed.

`W31_CONSUMER_CONTRACT.lean` proves the exact old W30 assertion with its original
definitions, checks the injective bounded-polynomial map, and constructs a
bounded reciprocal companion for every bounded input. It passes with empty
output. `W31_GLUE_CONTRACT.lean` proves the reciprocal compatibility prerequisite
and checks the types of the two remaining converse targets; it does not prove
them. `python3 W31_CHECK_SOURCE.py` checks caps, admissions, final logs, sorted
imports, new-module-only Lean scope, whitespace, the audit and both contracts.
No whole-library build or lint ran.
