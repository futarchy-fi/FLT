# Formal functions needed by the ample-neighborhood theorem

W96 first checked the finite flat divisor route. The existing
`CurveDivisorAmpleSupport.divisor_relativeAmple_iff_meets_components`
(the declaration is in namespace `FLT.Mazur.FCurve`) and
`GeneralizedCurveFiberAmple` prove ampleness over a field. They do not
construct a neighborhood on the base. `GeneralizedCurveAmpleSubgroup`
requires actual closed projective presentations on affine base opens.

The canonical section of O(D) is already global, but its generator open is
X minus D; affineness of that open over the base has not been established.
Finite flatness of D makes D affine over an affine base, not X minus D.
The exact sequences for O(nD) have quotients supported on D. Their higher
cohomology vanishes, but this alone does not show that H1(O(nD)) vanishes
or that enough sections lift from the fibre. The projective Serre theorem
requires the very ample presentation this argument is trying to produce.
Thus this attempted bypass stops at a missing relative theorem; this is
not a mathematical counterexample to the finite-divisor criterion.
No consumer hypothesis is weakened to assume relative ampleness.

## Precise target

For a proper map X → Spec A, A Noetherian local with maximal ideal m,
and an invertible sheaf L with ample closed-fibre restriction, prove that
H0(X,L^d) → H0(X_0,L_0^d) is surjective for all sufficiently large d.
This is the degree-zero consequence of Stacks 0D2M used by 0D2N.
Full 0D2N does not assume flatness or projectivity of X over A.

The formal-functions comparison required along this route is
completion_m H0(X,L^d) ≅ lim_n H0(X,L^d / m^(n+1)L^d), compatible with
all quotient and restriction maps. An abstract isomorphism without those
compatibilities does not suffice to lift sections. In particular an
arbitrary compatible formal section is not asserted to be algebraizable.

## Leaves and dependencies

Each implementation leaf must be at most 240 lines. The later rows are
bounded interfaces to split further if their proofs exceed that cap;
they are not assertions that the missing theory fits in one small proof.
Existing modules are reused without edits.

| Leaf | Concrete output | Dependencies |
| --- | --- | --- |
| F0a | Base-ring linear connecting maps, exactness and finite subobject/middle cohomology lemmas | `ModuleCohomologyRing`, `ModuleCohomologyExact` |
| F0b | All-degree finite base-ring cohomology, two-out-of-three and generic-rank-one devissage | F0a, `CoherentGenericRankOneCriterion` |
| F0c | All-degree finiteness under closed and acyclic direct image, plus closed projective presentations | F0b, existing ring-linear comparisons and projective finiteness |
| F1a | Closed projective embedding of the Noetherian affine-base Chow modification | `ChowAffineBaseGraphProductComparison`, finite Segre embedding |
| F1b | One Chow line very ample for both projections; simultaneous acyclic powers | F1a, `RelativeSerreVanishing` |
| F1c | Coherence of the Chow power direct image on each affine open | F1b, projective finiteness, affine sections localization |
| F1d | Closed Chow witness support and generic rank one over a Noetherian ring | F1c, existing generic-neighborhood and closed-stalk comparisons |
| F1e | Proper coherent cohomology finite over a Noetherian ring, all degrees | F0b-F0c, F1b-F1d |
| F2a | Actual m-adic coefficient quotients, transition maps and graded exact sequences | ideal multiplication and sheaf cokernels |
| F2b | Uniform Serre bound for the finite-type associated graded coefficient module | F2a, graded coherent Serre theorem (Stacks 30.19.3) |
| F2c | Vanishing on all infinitesimal fibres and surjective H0 transition maps | F2b, cohomology exact sequence |
| F3a | Artin-Rees control of cohomology filtrations for the proper coefficient system | F1e, F2a; Stacks 30.20.4 |
| F3b | H0 completion-to-inverse-limit comparison with quotient compatibility | F3a, completion and inverse-limit APIs; Stacks 30.20.5 |
| F3c | Eventual surjectivity onto the closed fibre, using induced-topology comparison | F2c, F3a-F3b; Stacks 30.20.4(3) |
| F4a | Lift a finite ample fibre presentation and shrink by properness (0D2N) | F3c, `ProperFiberNeighborhood` |
| F4b | Transfer through the proper finitely presented model | F4a, `ProperAmpleFiberModel` |

For the flat Mazur family, flatness can simplify the associated graded
pieces, but it does not identify a residue-field map as flat and therefore
does not permit applying `FlatGlobalSectionBaseChange` to that map.
Full proper-only 0D2S still requires proper inverse-system approximation;
one finitely presented cartesian model does not prove that full statement.
A7-A8 remain downstream, and the parallel D/G2 lanes remain separate.

## Recheck

Build each new module in the foreground with `LEAN_NUM_THREADS=2 lake build
FLT.Mazur.MODULE`; lint only that module with `lake exe runLinter
FLT.Mazur.MODULE`. Audit every new declaration with `#print axioms` against
`propext`, `Classical.choice`, `Quot.sound`. W96's untracked handoff records
which leaves were actually completed and their validation receipts.
