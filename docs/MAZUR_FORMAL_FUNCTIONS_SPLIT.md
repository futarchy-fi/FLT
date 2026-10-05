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
| F1b1 | One Chow line very ample for both projections | F1a, `RelativeVeryAmpleLineBundle` |
| F1b2 | Simultaneous acyclic powers with finite base-ring cohomology | F1b1, F0c, `RelativeSerreVanishing` |
| F1c1 | Chow affine pieces and overlaps localize over the base | F1b1, existing base-linear equalizer |
| F1c2 | Transport piece coordinates to the equalizer localization | F1c1 |
| F1c3 | Actual direct-image sections localize on each affine target open | F1c2, existing restriction comparisons |
| F1c4 | Finite sections and coherence of the Chow power direct image | F1c3, projective finiteness |
| F1d1 | Rank-one coordinates on the actual Chow direct-image generic stalk | F1b1, existing generic-neighborhood comparisons |
| F1d2 | Closed Chow witness support and residue rank one | F1c4, F1d1, existing closed-stalk comparisons |
| F1e | Proper coherent cohomology finite over a Noetherian ring, all degrees | F0b-F0c, F1b2, F1d2 |
| F2a1 | Actual ideal-adic coefficient quotients and compatible epimorphic transitions | ideal multiplication and sheaf cokernels |
| F2a2 | Canonical graded short exact sequences with ideal-annihilated kernels | F2a1, cokernel-composition snake lemma |
| F2a3 | Specialize to the base maximal ideal; compare powers, quotient pullback and tensor powers | F2a1-F2a2, base ideal pullback |
| F2b | Uniform Serre bound for the finite-type associated graded coefficient module | F2a3, graded coherent Serre theorem (Stacks 30.19.3) |
| F2c | Quotient vanishing and surjective H0 reductions from graded vanishing | F2a2, cohomology exact sequence; applying it needs F2b |
| F3a | Artin-Rees control of cohomology filtrations for the proper coefficient system | F1e, F2a3; Stacks 30.20.4 |
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

## W96 implementation boundary

`ModuleRingCohomologyExact`, `CoherentRingCohomologyFinite` and
`RingCohomologyFinitePushforward` supply F0a-F0c. The affine-base Chow
modules supply F1a-F1d2. `ProperRingCohomologyFinite` assembles F1e:
`FLT.Mazur.Chow.AffineBase.proper_coherent_hasFiniteRingCohomology`
proves all-degree finite cohomology for any coherent coefficient on a
proper scheme over a Noetherian ring (schemes in universe zero).
The ring action is the one induced by the specified structure morphism.
The rank-one witnesses and their cohomology finiteness are constructed.

`IdealAdicQuotient` constructs M / I^n M and its inverse system for an
actual ideal sheaf I. `IdealAdicGradedSequence` proves the canonical
short exact sequence with kernel I^n M / I^(n+1) M and its annihilation
by I. These are F2a1-F2a2, not yet the base-maximal-ideal identification.
`IdealAdicCohomology` supplies F2c as an implication from graded
vanishing, including surjectivity across any finite number of reductions.
It does not supply the uniform bound needed to apply that implication.

The next missing inputs are F2a3/F2b and F3a-F3c. In particular no theorem
here identifies completed H0 with the compatible quotient sections, nor
shows that original sections surject onto the closed fibre. L2, arbitrary
base transfer, A7-A8 and removal of `Mazur_statement` remain unproved.

## Recheck

Build each new module in the foreground with `LEAN_NUM_THREADS=2 lake build
FLT.Mazur.MODULE`; lint only that module with `lake exe runLinter
FLT.Mazur.MODULE`. Audit every new declaration with `#print axioms` against
`propext`, `Classical.choice`, `Quot.sound`. W96's untracked handoff records
which leaves were actually completed and their validation receipts.

## W97: base thickenings and compatible line quotients

The line-coefficient part of F2a3 is now constructed, including the actual
restriction maps. `BaseAdicThickening` extends an ideal J of R to X and
identifies its powers on every affine chart. `BaseAdicQuotientSpectrum`
identifies the resulting closed subscheme with
X × Spec(R / J^n), compatibly with the immersion into X. Specializing J
to `IsLocalRing.maximalIdeal R` gives the required local-base thickenings.
These statements do not assume flatness of the residue-field map.

`IdealAdicLineQuotient.lineQuotientClosedIso` identifies L / I^n L with
the closed pushforward of the actual pullback of L. Its projection is
proved to be the pullback adjunction unit. This comparison holds for any
scheme and line sheaf; it does not require Noetherianity.
`IdealAdicLineTower` compares every reduction and the inverse systems in
the locally Noetherian coherent setting used by the existing tower. It
also compares quotients of L^d with powers of its closed restriction,
including d = 0, and retains the unit compatibility.

This completes the geometric comparison for the line powers in the
stated H0-lifting target. A corresponding theorem for an arbitrary
coherent coefficient M is not claimed by these modules.

The next unresolved input is F2b: one Serre bound simultaneously valid
for every associated-graded degree. The existing
`AmpleLineBundle.coherent_vanishing` supplies a bound for one coherent
coefficient at a time, and `graded_idealKilled` supplies annihilation of
each graded piece. Neither supplies the finite-type graded sheaf and
uniform Serre argument of Stacks 30.19.3. The algebraic Rees-algebra API
in Mathlib is not a sheaf-cohomology theorem. No arbitrary maximum over
the infinitely many degree-wise bounds is taken here. F3a-F3c, L2 and
removal of `Mazur_statement` remain open.
