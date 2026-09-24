# Serre L2, attempt 2: geometric progress; full leaf still blocked

`FreyPackage.inertia_sub_one_sq_eq_zero_away` and the original
`characters_unramified_away` are **not proved**. No new admission was added.
The completed work proves Frey semistability and derives the split
multiplicative local inertia calculation from general Tate uniformization.
The good-reduction and nonsplit cases, and the local/global comparison,
still prevent assembly of the exact input from `Scratch/BLOCKED-a1.md`.

Checked at **2026-09-24 17:42 UTC**, implementation through `e34d430c`.
Evidence: the build, linter and constant-closure audit commands below all
returned exit 0. No push was made; scratch checks are uncommitted.

## Proved and committed

All three new modules are imported alphabetically from `FLT.lean`.

### `FLT/FreyCurve/Serre/Semistable.lean`

* `FreyCurve.c₄_int`: polynomial formula for the integral model (`bc09d3f7`).
* `FreyCurve.two_pow_eight_mul_Δ_int`: integral discriminant identity
  `2^8 * Δ = (abc)^(2p)` (`e97cd619`).
* `FreyCurve.map_c₄_ne_zero_of_map_Δ_eq_zero`: over any residue field,
  vanishing discriminant implies nonvanishing `c₄` (`c08418a3`).
* `FreyCurve.good_or_multiplicative_integral`: the normalized integral
  model has good or multiplicative reduction over every DVR (`af2cd142`).
* `FreyPackage.good_or_multiplicative`: the same conclusion for the actual
  rational Frey curve after base change (`e34d430c`). This proves the
  required minimality, rather than assuming a minimal model. It includes
  residue characteristic 2; it does not assert split reduction at 2.

These five results have only `propext`, `Classical.choice`, `Quot.sound`.
Thus Frey semistability is no longer a missing geometric hypothesis.

### `FLT/FreyCurve/Serre/RootsOfUnityInertia.lean`

* `IsLocalRing.eq_of_pow_eq_one_of_residue_eq`: reduction separates
  `n`-th roots of unity when `n` is a unit in the local ring (`b41846e7`).
* `ValuationSubring.inertia_fixes_of_pow_eq_one`: the actual valuation-ring
  inertia subgroup fixes those roots (`7ef6b60f`).

Both results have only `propext`, `Classical.choice`, `Quot.sound`.
The first uses Mathlib's uniqueness of a simple polynomial root; no
Henselian existence hypothesis or admitted cyclotomic theorem is used.

### `FLT/FreyCurve/Serre/TateInertia.lean`

* `WeierstrassCurve.exists_tatePoint_of_nsmul_eq_zero`: every `n`-torsion
  point has a representative `u` with `u^n = q^m` (`1aecf52d`).
* `WeierstrassCurve.exists_rootOfUnity_tatePoint_sub`: the difference
  `σ(P) - P` is the Tate point of an `n`-th root of unity (`b4e8b1f7`).
  In the proof that root is `σ(u)/u`; its power is one because `σ(q)=q`.
* `WeierstrassCurve.inertia_sub_sub_eq_zero_of_split_multiplicative`:
  `(σ-1)^2 P = 0` for prime-to-residue-characteristic torsion on any
  elliptic curve with split multiplicative reduction (`dcf3a030`).
  This derives the local conclusion from Tate theory, with no assumed
  torsion filtration and no assumed triviality of a torsion character.

These are stepping stones under ATTEMPT 2's explicit allowance for
existing general elliptic-curve admissions, not axiom-free final proofs.

## Exact transitive admission audit

`Scratch/TateInertiaAudit.lean` walks every referenced constant's type and
`ConstantInfo.value? (allowOpaque := true)`, including opaque proofs, and
records both direct admission sites and all reached axioms. It runs the
walk and `#print axioms` on **each of the ten new declarations**. Output is
preserved in `Scratch/TateInertiaAudit.out`.

The complete list of reached declarations directly containing `sorryAx` is:

1. `WeierstrassCurve.tateEquivSepClosure`, in
   `FLT/KnownIn1980s/EllipticCurves/TateCurve.lean`.
2. `WeierstrassCurve.tatePoint_galois`, in the same file.

The torsion-representative lemma reaches only (1). The deviation and
square-unipotence lemmas reach exactly (1) and (2), so their axiom lists
are `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
The other seven new declarations reach neither admission and have only
the three standard axioms. No `knownin1980s` axiom, torsion-cardinality
admission, Mazur theorem, irreducibility placeholder, or FLT conclusion
occurs in any new proof's dependency closure.

## Exact next geometric statement

The good-reduction branch needs prime-to-residue-characteristic torsion
to be fixed by inertia **without** a reduction-map hypothesis. The following
proposition is elaborated as `NeededGoodReductionInput` in the uncommitted
`Scratch/NextGoodReductionInput.lean`; it is not asserted as a theorem:

```lean
def NeededGoodReductionInput
    (R K Ω : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [DecidableEq Ω]
    (A : ValuationSubring Ω) (n : ℕ) : Prop :=
  (A.comap (algebraMap K Ω)).toSubring = (algebraMap R K).range →
  IsUnit (n : A) →
  ∀ (σ : A.decompositionSubgroup K), σ ∈ A.inertiaSubgroup K →
    ∀ P : (E⁄Ω).Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom P = P
```

The existing `WeierstrassCurve.torsion_unramified_of_good_reduction` does
not supply this: its explicit `hreduction` hypothesis already requires
an injective, inertia-invariant reduction map. Constructing that map is
the missing general elliptic-curve input. `torsion_flat_of_good_reduction`
is an existing admission, but its finite-flat Hopf-algebra conclusion
still requires a prime-to-residue-characteristic finite-flat-to-unramified
theorem; the comments discussing that implication are not Lean proofs.
`GaloisModule.IsFiniteFlat.quotient` only supplies quotient closure.

Two further boundaries remain after that:

* **Nonsplit multiplicative reduction.** The existing
  `exists_quadraticTwist_hasSplitMultiplicativeReduction` constructs the
  quadratic twist, internally using
  `exists_unramified_extension_of_residueField`, but its public conclusion
  discards the unramified extension witness. Retain that witness, prove
  that inertia fixes the splitting extension, and transport the new Tate
  result using `quadraticTwistPointEquiv_galois`. The existence of a
  quadratic twist alone does not show its character is inertia-trivial.
* **The representation used by the leaf.** The new Tate theorem concerns
  `Affine.Point.map` over a separable closure and
  `ValuationSubring.inertiaSubgroup`. The leaf uses `GaloisRep.toLocal`
  on global geometric torsion. Its `localInertiaGroup` is defined through
  the maximal ideal of `IntegralClosure` in the local algebraic closure.
  Identify these inertia actions, transport points through the chosen
  embedding of algebraic closures, and pass to `Module.End` using the
  injectivity of point base change and `galoisRep_apply`.

The corrected smaller completed statement is
`inertia_sub_sub_eq_zero_of_split_multiplicative`, together with unconditional
Frey semistability. Neither is being relabelled as the full Serre leaf.

## Verification

```sh
lake build FLT.FreyCurve.Serre.AwayFromP \
  FLT.FreyCurve.Serre.RootsOfUnityInertia \
  FLT.FreyCurve.Serre.Semistable FLT.FreyCurve.Serre.TateInertia
lake exe runLinter FLT.FreyCurve.Serre.AwayFromP \
  FLT.FreyCurve.Serre.RootsOfUnityInertia \
  FLT.FreyCurve.Serre.Semistable FLT.FreyCurve.Serre.TateInertia
lake env lean Scratch/TateInertiaAudit.lean
lake env lean Scratch/NextGoodReductionInput.lean
git diff --check d2f5e947
```

All four modules build and pass the repository linter. New declarations
have docstrings and no unused arguments; headers use the requested author
and copyright. No new `sorry`, `axiom`, `native_decide`, or `knownin1980s`
occurs in the new source. The original axiom-free acceptance criterion
for the full leaf remains unmet, as explicitly allowed for a partial
ATTEMPT 2 report. No final-leaf completion commit was manufactured.
