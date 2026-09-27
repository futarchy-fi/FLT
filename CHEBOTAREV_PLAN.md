# Chebotarev plan for B5

Checked at 2026-09-27 14:10 UTC in this worktree. FLT source commit:
`8b2ec5b62ef40a1a6182a5db9416678d06519868`; Mathlib:
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
This is a source-backed plan, not a proof or a claim that the admission is closed.
All names introduced below are **proposed**, unless listed in the inventory.
Lean blocks are statement sketches, not elaboration-tested code.

Recommend **C, using the weak part of B**: prove that every element of a finite
Galois quotient is a power of a conjugate of some Frobenius outside any finite
set. Dedekind zeta and cyclic fixed fields should supply this. B5 only needs the
property “has a nonzero fixed vector”, which survives powers and conjugation.
Full Chebotarev, Hecke L-functions, and Artin reciprocity are unnecessary for
this route to B5. There is still substantial missing prime-splitting machinery.

If the deliverable is specifically a proof of
`GaloisRepresentation.B5Inputs.chebotarev_frobenius_dense` with its present type,
use A below. The recommended C route removes that theorem from B5's proof path;
it does **not** prove its stronger statement. Do not mark that admission closed
when only C is complete.

## What B5 actually uses

`FLT/GaloisRepresentation/HardlyRamified/B5Inputs.lean:492` is the only call to
`chebotarev_frobenius_dense` found under `FLT`. Its enclosing theorem is
`GaloisRepresentation.B5Inputs.not_isIrreducible_of_frobenius_traces` (line 469).
It obtains equality of representation values up to conjugation solely to deduce

```lean
∀ g, (ρ g).trace k V = 1 + (ρ g).det
```

and applies the already-proved
`GaloisRepresentation.B5Inputs.not_isIrreducible_of_trace_eq_one_add_det`.
The caller is `GaloisRepresentation.IsHardlyRamified.not_isIrreducible_of_prime_field`
in `FLT/GaloisRepresentation/HardlyRamified/PrimeField.lean:42`, with the application
at line 76. Compatibility and the three-adic input give the required traces;
`hρ.det` gives the determinant. The generic trace theorem itself does not assume
hardly ramified, an abelian image, or a cyclotomic factorization of `ρ`.

In dimension two, `tr A = 1 + det A` is equivalent to `det(A - 1) = 0`, hence to
`∃ v ≠ 0, A v = v`. If `A` has such a vector, so do `A^n` and every conjugate.
Thus even equality of characteristic polynomials is more than B5 needs.
Coprime powers are sufficient; arbitrary powers in the conclusion below are
convenient and weaker still.

This is a mathematical simplification with a complete paper argument:

1. For a finite Galois extension `L/ℚ` and `g ∈ Gal(L/ℚ)`, put `H = ⟨g⟩`,
   `F = L^H`. Then `L/F` is cyclic.
2. For every subgroup `D ≤ H`, primes of `F` whose Frobenius in `H` lies in `D`
   are the primes splitting completely in `L^D/F`. Their logarithmic Dirichlet
   density is `|D|/|H|`, obtained from the zeta pole of `L^D` and prime splitting.
3. Inclusion-exclusion over the maximal subgroups of `H` gives density
   `φ(|H|)/|H| > 0` for primes whose Frobenius generates `H`.
4. Prime ideals of `F` of residue degree greater than one over `ℚ` have bounded
   prime sum as `s → 1+`; they have density zero. Remove them and all primes over
   the finite excluded rational set, including primes ramified in `L/ℚ`.
5. A remaining prime has norm a rational prime `q`. Its Frobenius in `L/F`,
   included in `Gal(L/ℚ)`, is a rational Frobenius at `q`. It generates `H`, so
   `g` is its nonnegative power. Arbitrary choices of primes/embeddings require
   conjugation. This proves the power-cover statement.
6. Apply the fixed-vector property to `ρ(Frob_q)`, transport by power and
   conjugation, convert back to `tr = 1 + det`, and use the existing rank-two
   reducibility theorem.

Step 3 works also for `H = 1`: the intersection indexed by no maximal subgroups
is the whole group and the density is 1. Step 4 needs positive density, not just
infinitely many prime ideals; otherwise every available prime could have higher
residue degree. A chosen rational Frobenius is compared only at primes unramified
in the finite extension.

## Existing declarations and trust checks

Paths prefixed `M/` mean `.lake/packages/mathlib/Mathlib/`; `F/` means `FLT/`.
The identifiers below were found in these exact files, not inferred from names
of folders or from external versions of Mathlib.

| Ref | Existing declarations | File / role |
|---|---|---|
| E1 | `GaloisRepresentation.B5Inputs.chebotarev_frobenius_dense_of_surjective_group_case` | `F/GaloisRepresentation/HardlyRamified/B5Inputs.lean:259`; monoid-to-image-group reduction already done |
| E2 | `GaloisRepresentation.B5Inputs.chebotarev_frobenius_dense_of_factors_cyclotomic`, `modularCyclotomicCharacter_adicArithFrob`, `cyclotomicCharacter_adicArithFrob` in the same namespace | Same file, lines 418, 386, 352; cyclotomic case and determinant evaluation |
| E3 | `GaloisRepresentation.B5Inputs.not_isIrreducible_of_trace_eq_one_add_det` | `F/GaloisRepresentation/HardlyRamified/TraceReducibility.lean:88`; elementary proof over any field, with no semisimplicity assumption |
| E4 | private `det_sub_one_eq_zero`, private `not_irreducible_of_covector` | Same file, lines 73 and 30; useful proof bodies, **not public reusable declarations** |
| E5 | `NumberField.dedekindZeta`, `NumberField.dedekindZeta_residue`, `NumberField.dedekindZeta_residue_pos`, `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` | `M/NumberTheory/NumberField/DedekindZeta.lean:49,56,65,77` |
| E6 | `Chebotarev.dedekindZeta_eq_tprod_primeIdeal`, `Chebotarev.dedekindZeta_re_pos_of_one_lt`, `Chebotarev.hasSum_nonzeroIdeal_absNorm_cpow`, `Chebotarev.summable_idealNormMultiplicity_mul_cpow_neg` | `F/AINTLIB/CebotarevDensity/NumberFieldEulerProduct.lean:841,850,548,316`; existing vendored Euler-product proof |
| E7 | `NumberField.Set.primeIdealZetaSum`, `NumberField.Set.HasDirichletDensity`, `NumberField.Set.primeIdealZetaSum_le_card_of_finite` | `M/NumberTheory/NumberField/DirichletDensity.lean:58,91,75`; density uses the **all-prime-ideal sum** as denominator |
| E8 | `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`, `InfiniteGalois.normalAutEquivQuotient`, `InfiniteGalois.isOpen_iff_finite`, `InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois` | `M/FieldTheory/Galois/Infinite.lean:196,228,241,288` |
| E9 | `InfiniteGalois.restrictNormalHom_continuous`, `AlgEquiv.restrictNormalHom_surjective` | `M/FieldTheory/Galois/Profinite.lean:148`; `M/FieldTheory/Normal/Basic.lean` (restriction surjectivity) |
| E10 | `arithFrobAt`, `IsArithFrobAt.arithFrobAt`, `IsArithFrobAt.conj`, `IsArithFrobAt.mul_inv_mem_inertia`, `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` | `M/RingTheory/Frobenius.lean:260,264,205,200,164`; algebraic Frobenius and uniqueness modulo inertia |
| E11 | `Field.AbsoluteGaloisGroup.adicArithFrob`, `Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob`, `Field.absoluteGaloisGroup.lift_map` | `F/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean:165,170,53`; B5's actual chosen local element |
| E12 | `NumberField.InertiaComparison.exists_inducedPrime_completion_embedding`, `NumberField.InertiaComparison.inducedPrime_eq_of_completion_embedding` | `F/AbsoluteGaloisGroup/CompletionComparison.lean:96,80`; ingredients for comparing finite primes with completions, not the required Frobenius comparison theorem |
| E13 | `Ideal.sum_ramification_inertia`, `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, `Ideal.inertiaDegIn_mul_inertiaDegIn`, `Ideal.exists_smul_eq_of_isGaloisGroup` | `M/NumberTheory/RamificationInertia/Basic.lean:614`; `.../Galois.lean:222,192,127` |
| E14 | `Ideal.absNorm_pow_inertiaDeg` | `M/RingTheory/RamificationInertia/Inertia.lean:185` |
| E15 | `NumberField.not_dvd_discr_iff_isUnramifiedIn`, `NumberField.discr_ne_zero` | `M/NumberTheory/NumberField/Discriminant/Different.lean:192`; `.../Discriminant/Defs.lean:41`; bound ramification by absolute discriminant |
| E16 | `Ideal.finite_setOfPred_absNorm_le`, `Ideal.tendsto_norm_le_div_atTop₀` | `M/RingTheory/Ideal/Norm/AbsNorm.lean:502`; `M/NumberTheory/NumberField/Ideal/Asymptotics.lean:128` |
| E17 | `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`, `Ideal.Quotient.stabilizerHom_surjective`, `IsFractionRing.ker_stabilizerHom` | `M/FieldTheory/Finite/Basic.lean:392`; `M/RingTheory/Invariant/Basic.lean:360,322` |
| E18 | `Subgroup.exists_zpowers_eq_of_zpowers_eq_top`, `Subgroup.zpowers_eq_zpowers_iff'` | `M/GroupTheory/SpecificGroups/Cyclic.lean:489,464`; subgroup arithmetic |
| E19 | `DirichletCharacter.LFunction_eq_LSeries`, `DirichletCharacter.differentiable_LFunction`, `DirichletCharacter.LFunction_apply_one_ne_zero`, `Nat.forall_exists_prime_gt_and_eq_mod` | `M/NumberTheory/LSeries/DirichletContinuation.lean:75,98`; `.../Nonvanishing.lean:408`; `.../PrimesInAP.lean:442` |
| E20 | `NumberField.partialZeta`, `NumberField.partialZeta_analyticOn`, `NumberField.sum_partialZeta_eq_dedekindZeta` | `F/NumberField/Zeta/Partial.lean:42,172,181`; ordinary ideal classes, analytic only on `Re s > 1` |

E5's exact available result is

```lean
Tendsto (fun s : ℝ ↦ (s - 1) * NumberField.dedekindZeta K s)
  (𝓝[>] 1) (𝓝 (NumberField.dedekindZeta_residue K))
```

with a strictly positive real residue. This is enough for B/C. It is not a
meromorphic continuation theorem: `dedekindZeta` is defined as an `LSeries`,
whose values outside convergence must not be used as an analytic continuation.
No completed-zeta functional equation or zero-free region is required here.

The Mathlib source search for `chebotarev`, `hecke character`, `HeckeCharacter`,
`artin reciprocity`, and `class field theory` found no relevant theorem/API.
`M/NumberTheory/HeckeRing/Defs.lean` defines double-coset Hecke rings, not Hecke
characters or their L-functions. E19 handles characters of `(ZMod n)ˣ`, not
characters of ray class groups over an arbitrary number field. E20 is not a
ray-class prime theorem. This is a statement about the pinned checkout; it
makes no claim about unvendored upstream work.

A read-only Lean check importing B5Inputs and NumberFieldEulerProduct printed
axioms for E5's residue limit, E6's Euler product, E3, E2's cyclotomic density,
and the target admission. All four existing inputs use only `propext`,
`Classical.choice`, and `Quot.sound`; the target additionally uses `sorryAx`.
Command: `lake env lean /tmp/chebotarev-plan-audit.lean` (exit 0). The complete
reproducible check is at the end of this plan. No new Lean file was added.

## Statement conventions and sizes

For all number-field sketches, bind `(K L : Type*) [Field K] [NumberField K]
[Field L] [NumberField L] [Algebra K L]`; add `[IsGalois K L]` where stated.
For towers, install the compatible algebra and scalar-tower instances. Use
`FiniteDimensional K L` inferred from number-field hypotheses. A worker must
make these instances explicit when elaborating a statement.

Proposed notation/API (definitions, not arithmetic assumptions):

```lean
abbrev Prime (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)
def norm (v : Prime K) : ℕ := v.asIdeal.absNorm
def ell (s : ℝ) : ℝ := Real.log (1 / (s - 1))
def ps (T : Set (Prime K)) (s : ℝ) : ℝ :=
  NumberField.Set.primeIdealZetaSum T s
def LogDensity (T : Set (Prime K)) (d : ℝ) : Prop :=
  Tendsto (fun s : ℝ => ps T s / ell s) (𝓝[>] 1) (𝓝 d)
def Unram (K L) (v : Prime K) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal
def HasFrob (K L) (v : Prime K) (a : Gal(L/K)) : Prop :=
  ∃ w : Prime L, w.asIdeal.under (𝓞 K) = v.asIdeal ∧
    IsArithFrobAt (𝓞 K) a w.asIdeal
```

Use the natural action of `Gal(L/K)` on `𝓞 L`. Proposed `frob K L v : Gal(L/K)`
is the Frobenius at one chosen prime above `v`, obtained from E10. Its class
is independent of that choice only at unramified primes. Define
`Split K L = {v | Unram K L v ∧ frob K L v = 1}` and
`Generators K L = {v | Unram K L v ∧ Subgroup.zpowers (frob K L v) = ⊤}`.
For `F/ℚ`, define `DegreeOne F v := Nat.Prime (norm v)`; the norm formula E14
identifies this with residue degree one. These predicates are all new wrappers.

`QFrob q hq : Field.absoluteGaloisGroup ℚ` abbreviates the exact
`Field.absoluteGaloisGroup.map (algebraMap ℚ (...adicCompletion ℚ))
(Field.AbsoluteGaloisGroup.adicArithFrob ...)` expression in the target.
It must not choose another algebraic-closure embedding.

A **capped worker** means one worker for about 2–4 hours. Estimates below are
new Lean proof lines, excluding reused files; hours are rough engineering
estimates, conditional on the stated dependencies being available.
S = 20–100 lines / 1–4 hours, plausible capped work; M = 100–300 / 1–3 days;
L = 300–800 / 3–10 days; XL = more than 800 / weeks or more. M/L/XL leaves are
honest work boundaries, **not** tickets to hand to a capped worker unchanged.
No estimate treats “import class field theory” as a small task.

## Dependency tree

```text
C-result: B5 without full Chebotarev
├─ C4 integrate existing trace criterion
│  ├─ C1 trace iff fixed vector
│  ├─ C2 fixed vector under powers/conjugation
│  └─ C3 conditional propagation wrapper
└─ W3 power-cover in a finite quotient
   ├─ G1 open kernel; G2 finite Galois quotient realization
   ├─ G3 finite ramified set; G4 chosen local/global Frobenius comparison
   └─ W2 degree-one generator prime in L / L^<g>
      ├─ W1 cyclic generator density
      │  ├─ H1 cyclic subgroup inclusion-exclusion
      │  ├─ H2 Frobenius restriction / subgroup membership
      │  └─ B4 splitting-completely density for all intermediate fields
      │     ├─ B1 Frobenius order / residue degree
      │     ├─ B2 prime splitting sum
      │     ├─ B3 nonsplit contribution bounded
      │     └─ Z4 prime-ideal sum / ell → 1
      │        ├─ Z1 logarithm of zeta / ell → 1 (E5)
      │        ├─ Z2 prime-ideal summability (E6)
      │        └─ Z3 log Euler product remainder bounded (E6)
      ├─ D1 higher relative degree sum bounded
      ├─ D2 positive density survives finite / bounded removals
      └─ H3 degree-one Frobenius in a tower

A-result: existing full chebotarev_frobenius_dense, same type
├─ E1 monoid reduction, G1–G4 finite quotient / Frobenius bridge
└─ A9 Deuring reduction for a specified generator
   ├─ D1, D2, H3 (same degree-one extraction)
   └─ A8 cyclic exact-class positive density
      ├─ A1 ray modulus, ray ideal group and ray class quotient
      ├─ A2 ray class finiteness
      ├─ A3 Artin reciprocity with prime compatibility
      ├─ A4 finite-order Hecke series and Euler product
      ├─ A5 holomorphy near 1 for nontrivial characters
      ├─ A6 nonvanishing at 1
      └─ A7 character orthogonality and prime-sum asymptotics
```

G/H/B/Z/D are shared arithmetic work; C1/C2/G1/Z1 are useful initial bounded
work. C3 is explicitly conditional until W3 is proved.

## C: B5-specific algebra leaves

Common variables here are `[Field k] [Group G] [AddCommGroup V] [Module k V]
[FiniteDimensional k V]`. These statements do not require characteristic zero,
semisimplicity, or finite `k`.

**C1 — fixed-vector criterion. S, capped: yes. Existing: E3/E4.**

```lean
theorem trace_eq_one_add_det_iff_fixedVector
    (hV : Module.finrank k V = 2) (A : Module.End k V) :
    A.trace k V = 1 + A.det ↔ ∃ v : V, v ≠ 0 ∧ A v = v
```

Copy/generalize E4's two-by-two determinant computation, then use
`LinearMap.det_eq_zero_iff_ker_ne_bot` (already used by E3). Prove both
directions; the reverse is needed after transport. Keep it public.

**C2 — fixed-vector transport. S, capped: yes. Existing: E3's conjugation and
linear-map algebra; `map_mul`, `map_pow`, group inverses.**

```lean
theorem fixedVector_conj_pow (ρ : Representation k G V)
    (a t : G) (n : ℕ) (h : ∃ v : V, v ≠ 0 ∧ ρ a v = v) :
    ∃ w : V, w ≠ 0 ∧ ρ (t * a^n * t⁻¹) w = w
```

Use `w = ρ t v`; the inverse proves it is nonzero. Induct on `n`. No
coprimality is needed in this direction; this avoids fragile eigenvalue proofs.

**C3 — conditional propagation. S, capped: yes, conditional wrapper only.
Existing: E1's units/image construction and E2. Depends on C1/C2.**

```lean
def PowerFrobCover (f : Field.absoluteGaloisGroup ℚ →ₜ* M)
    (S : Finset (Prime ℚ)) (N : ℕ) : Prop :=
  ∀ g, ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
    ∃ (σ : Field.absoluteGaloisGroup ℚ) (n : ℕ),
      f g = f (σ * (QFrob q hq)^n * σ⁻¹)

theorem trace_identity_of_powerFrobCover
    (hV : Module.finrank k V = 2) (ρ : GaloisRep ℚ k V)
    (S : Finset (Prime ℚ)) (N : ℕ)
    (hc : PowerFrobCover ρ S N)
    (hF : ∀ q (hq : q.Prime), N ≤ q →
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      (ρ (QFrob q hq)).trace k V = 1 + (ρ (QFrob q hq)).det) :
    ∀ g, (ρ g).trace k V = 1 + (ρ g).det
```

Here additionally install the finite discrete module topology from B5Inputs
when forming `PowerFrobCover ρ`. Retain the finite-field hypotheses of the
current B5 theorem. This wrapper alone does not discharge arithmetic.

**C4 — replace the B5 call. S, capped: yes after W3. Existing: E2/E3 and the
body of `not_isIrreducible_of_frobenius_traces`.**
Keep that theorem's exact current signature. Use W3/C3 with `N = p + 1` and
`hdet` plus `cyclotomicCharacter_adicArithFrob` to supply `hF`; conclude by E3.
The acceptance statement is the existing `¬ ρ.IsIrreducible`, with no added
hypothesis. Do not change the callers in PrimeField or assume that `ρ` factors
through the cyclotomic character. Audit its axioms to show the Chebotarev
`sorryAx` dependency has disappeared; other upstream B5 admissions are separate.

## G: finite quotient and Frobenius interfaces

**G1 — open kernel. S, capped: yes. Existing: E8/E9 and discrete continuity.**
For `[Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]`:

```lean
theorem isOpen_ker (f : Field.absoluteGaloisGroup ℚ →ₜ* G) :
  IsOpen (f.toMonoidHom.ker : Set (Field.absoluteGaloisGroup ℚ))
```

Use the preimage of `{1}`. Normality is the existing kernel instance; closedness
follows from discreteness as well.

**G2 — realize the quotient. M, capped: no. Existing: E8/E9, E1's range step.**

```lean
theorem exists_finiteGalois_realization
    (f : Field.absoluteGaloisGroup ℚ →ₜ* G) (hf : Function.Surjective f) :
  ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L)
    (e : Gal(L/ℚ) ≃* G),
      ∀ g, e (AlgEquiv.restrictNormalHom L g) = f g
```

Take the fixed field of `ker f`. Show its fixing subgroup is exactly the
kernel, obtain finite dimensionality from openness, and compose the two
quotient equivalences. Type universes and the topology on the image need care.

**G3 — finite exceptional primes. S–M, capped: possible for `ℚ` only.
Existing: E15/E16.**

```lean
theorem finite_ramified_rational (L : Type*) [Field L] [NumberField L] :
  {q : ℕ | q.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 L)
    (Ideal.span {(q : ℤ)})}.Finite
```

Bound this set by prime divisors of `NumberField.discr L`. For relative
extensions use primes above rational divisors of the absolute discriminant of
the top field; a sharp relative discriminant API is not needed. The finite
pullback of a finite set under contraction also needs a finite-fiber lemma
from E13. Transport between `ℤ` and `𝓞 ℚ` explicitly.

**G4 — compare B5's chosen lift. L, capped: no. Existing: E10–E12.**
For finite Galois `L/ℚ` inside the algebraic closure:

```lean
theorem hasFrob_restrict_QFrob (q : ℕ) (hq : q.Prime)
    (hu : Unram ℚ L hq.toHeightOneSpectrumRingOfIntegersRat) :
  HasFrob ℚ L hq.toHeightOneSpectrumRingOfIntegersRat
    (AlgEquiv.restrictNormalHom L (QFrob q hq))
```

First restrict the local integral-closure Frobenius congruence to `𝓞 L`, using
the embedding in E11; identify the contracted prime via E12; identify the
residue cardinality with `q`. Uniqueness at an unramified prime and transitivity
on primes then give conjugacy with the independently chosen `frob`. Do not
assume that chosen embeddings agree definitionally. Subtasks are congruence
restriction (M), prime/completion comparison (M), and conjugacy assembly (S).
Their precise outputs are, respectively, `IsArithFrobAt ...`, the `under`
equality in `HasFrob`, and
`IsConj (restrictNormalHom L (QFrob q hq)) (frob ℚ L vq)`.

## Z and D: the analytic leaves needed for B/C

**Z1 — logarithm from the known residue. S, capped: yes. Existing: E5/E6.**

```lean
theorem log_dedekindZeta_asymptotic (K : Type*) [Field K] [NumberField K] :
  Tendsto (fun s : ℝ =>
    Real.log (NumberField.dedekindZeta K (s : ℂ)).re / ell s)
    (𝓝[>] 1) (𝓝 1)
```

Use the real part of the residue limit and positivity. Write the logarithm as
`ell s + log ((s-1) * ζ_K(s).re)`. The second term tends to a finite constant;
`ell s → +∞`. No differentiation or analytic continuation.

**Z2 — prime sums converge. S–M, capped: possible. Existing: E6/E14.**

```lean
theorem summable_primeNorm (s : ℝ) (hs : 1 < s) :
  Summable (fun v : Prime K => (norm v : ℝ)^(-s))
```

Embed prime ideals into nonzero integral ideals and use E6's absolute
summability. This also makes all later subtype `tsum` decompositions legitimate.
A `tsum` over a nonsummable family is zero in Lean; never use it as a divergent
series without first checking summability for each `s > 1`.

**Z3 — logarithmic Euler-product error. M, capped: no. Existing: E6, Z2.**

```lean
theorem log_zeta_sub_primeSum_bounded :
  Asymptotics.IsBigO (𝓝[>] (1 : ℝ))
    (fun s => Real.log (NumberField.dedekindZeta K (s : ℂ)).re -
      ps (Set.univ : Set (Prime K)) s) (fun _ => (1 : ℝ))
```

Split into two proof leaves if dispatched: (i) for real `s > 1`, log zeta is
`∑' v, -log (1 - (norm v : ℝ)^(-s))` (100–200 lines, M), by positive finite
Euler products and convergence; (ii) uniformly for `1 < s < 3/2`, the difference
from `∑' v, (norm v)^(-s)` is bounded by a constant times
`∑' v, (norm v)^(-2)` (80–180 lines, S–M). Use `norm v ≥ 2` and the scalar
Taylor bound on `[0, 1/2]`. Do not infer a logarithm-of-`tprod` identity without
nonzero/positivity and convergence side conditions.

**Z4 — normalize prime sums. S, capped: yes after Z1–Z3. Existing: E7.**

```lean
theorem logDensity_univ : LogDensity (Set.univ : Set (Prime K)) 1
theorem logDensity_iff_hasDirichletDensity (T : Set (Prime K)) (d : ℝ) :
  LogDensity T d ↔ NumberField.Set.HasDirichletDensity T d
```

The second statement uses the first and limit-of-quotient algebra. Prefer
`LogDensity` internally; supply this bridge rather than silently identifying
the two different denominators.

**D1 — higher residue degrees are negligible. M, capped: no. Existing:
E13/E14, Z2. For any finite extension `L/K` (not necessarily Galois):**

```lean
def HigherDegree (K L) : Set (Prime L) :=
  {w | ∃ v : Prime K, w.asIdeal.under (𝓞 K) = v.asIdeal ∧
      2 ≤ w.asIdeal.inertiaDeg (𝓞 K)}
theorem higherDegree_primeSum_bounded :
  Asymptotics.IsBigO (𝓝[>] (1 : ℝ))
    (ps (HigherDegree K L)) (fun _ => (1 : ℝ))
```

Each term is bounded by `norm v ^ (-2)` for `s > 1`; at most `[L:K]` primes lie
over `v`. Finite-fiber reindexing and the `e f` sum are the main Lean work.
In particular apply this with `K = ℚ` and `L = F` even when `F/ℚ` is nonnormal.

**D2 — discard negligible sets and choose a large norm. S–M, capped: possible.
Existing: E7/E16, Z2.**

```lean
theorem logDensity_diff (T U : Set (Prime K)) (d : ℝ)
    (hT : LogDensity T d)
    (hU : Asymptotics.IsBigO (𝓝[>] (1 : ℝ)) (ps U) (fun _ => (1 : ℝ))) :
  LogDensity (T \ U) d

theorem exists_norm_ge_of_logDensity_pos
    (T : Set (Prime K)) (d : ℝ) (hd : 0 < d) (hT : LogDensity T d)
    (S : Finset (Prime K)) (N : ℕ) :
  ∃ v ∈ T, v ∉ S ∧ N ≤ norm v
```

For the first, bound `T ∩ U` using nonnegative summands. For the second,
finite sets have bounded sums and bounded-norm ideals form a finite set.
These are separate capped candidates once the normalized-limit API is settled.

## B: what the zeta pole proves

A zeta-only implementation naturally proves splitting-completely density and
rational conjugacy (conjugacy of generated cyclic subgroups). Those statements
suffice for C. They do not separate two different generators of a cyclic group.

**B1 — Frobenius order equals residue degree. M, capped: no. Existing:
E10/E13/E17.**

```lean
theorem orderOf_frob_eq_inertiaDeg
    (v : Prime K) (w : Prime L)
    (hw : w.asIdeal.under (𝓞 K) = v.asIdeal) (hu : Unram K L v) :
  orderOf (frob K L v) = w.asIdeal.inertiaDeg (𝓞 K)
```

Identify the decomposition group modulo inertia with the residue Galois group;
unramifiedness kills inertia. E17 supplies the order of residue Frobenius.
First prove this for the chosen prime, then use constant residue degree in a
Galois extension. In particular `frob = 1` iff every prime above `v` has degree 1.

**B2 — prime fibers and their contributions. M, capped: no. Existing:
E13/E14.**

```lean
theorem sum_norm_powers_over_unramified (v : Prime K) (hu : Unram K L v)
    (s : ℝ) :
  ∑ w : Ideal.primesOver v.asIdeal (𝓞 L), (w.1.absNorm : ℝ)^(-s) =
    (Nat.card (Ideal.primesOver v.asIdeal (𝓞 L)) : ℝ) *
      (norm v : ℝ)^(-(s * v.asIdeal.inertiaDegIn (𝓞 L)))
```

Install the finite `primesOver` type. Together with E13 and `e=1`, split primes
contribute exactly `[L:K] * (norm v)^(-s)`; nonsplit primes have degree at least 2.

**B3 — remove all other fibers. S–M after D1/B1/B2; capped: possible.
Existing: G3 and E13.**

```lean
theorem primeSum_sub_splitPrimeSum_bounded :
  Asymptotics.IsBigO (𝓝[>] (1 : ℝ))
    (fun s => ps (Set.univ : Set (Prime L)) s -
      (Module.finrank K L : ℝ) * ps (Split K L) s) (fun _ => (1 : ℝ))
```

Ramified prime fibers are finite; nonsplit unramified fibers have higher degree.
This is where reindexing by contraction and finite ramification are required.

**B4 — splitting-completely density. S, capped: yes after B3/Z4.**

```lean
theorem logDensity_split :
  LogDensity (Split K L) (1 / (Module.finrank K L : ℝ))
```

Apply Z4 for `L`, divide B3 by `ell`, and use `[L:K] > 0`. No Artin/Hecke
L-function enters this argument.

**H1 — finite cyclic inclusion-exclusion. M, capped: no as a combined task.
Existing: E18.**
For a finite cyclic group `H`, let `Max H` be the finite type of maximal proper
subgroups and `D J = ⨅ D ∈ J, D` for a finite subset `J` of `Max H`. Proposed
statements, with subgroup indicators valued in `ℝ`:

```lean
theorem generator_indicator (a : H) :
  (if Subgroup.zpowers a = ⊤ then (1 : ℝ) else 0) =
    ∑ J ∈ (Finset.univ : Finset (Max H)).powerset,
      (-1 : ℝ)^J.card * (if a ∈ D J then 1 else 0)

theorem generator_density_coefficient :
  (∑ J ∈ (Finset.univ : Finset (Max H)).powerset,
    (-1 : ℝ)^J.card * (Nat.card (D J) : ℝ) / Nat.card H) =
      (Nat.totient (Nat.card H) : ℝ) / Nat.card H
```

The first is a general finite inclusion-exclusion leaf (S–M). The second is a
cyclic-group counting leaf (S–M): average the first over `H` and count generators.
An equivalent proof uses Möbius inversion over divisors. Choose whichever API
elaborates more cleanly; do not build a general Burnside ring for this task.

**H2 — subgroup membership and subfield splitting. M, capped: no. Existing:
E8/E10/E18, B1.**
For cyclic `Gal(L/K)` and `D : Subgroup Gal(L/K)`:

```lean
theorem frob_mem_iff_split_fixedField (v : Prime K) (hu : Unram K L v) :
  frob K L v ∈ D ↔ v ∈ Split K (IntermediateField.fixedField D)
```

Restriction of Frobenius to the fixed field is its Frobenius class; cyclicity
makes every subgroup normal and removes conjugacy ambiguity. Keep `hu`:
`Split K (L^D)` by itself does not assert that `v` is unramified in `L`.
For densities remove the additional finite ramified set using D2/G3.

**H3 — degree-one tower comparison. M, capped: no. Existing: E10/E14.**
For `F` intermediate in finite Galois `L/ℚ`, let
`incl : Gal(L/F) →* Gal(L/ℚ)` be restriction of scalars. Then

```lean
theorem hasFrob_tower_degreeOne (v : Prime F) (q : ℕ) (hq : q.Prime)
    (hv : norm v = q) (a : Gal(L/F)) (ha : HasFrob F L v a) :
  HasFrob ℚ L hq.toHeightOneSpectrumRingOfIntegersRat (incl a)
```

The powers in both Frobenius congruences are the same `q`; contraction identifies
the rational prime. In general relative Frobenius corresponds to a *power* of
rational Frobenius, so the norm hypothesis cannot be omitted.

**W1 — cyclic generator density. S–M after H1/H2/B4/D2; capped: possible.**

```lean
theorem logDensity_generators [IsCyclic Gal(L/K)] :
  LogDensity (Generators K L)
    ((Nat.totient (Nat.card Gal(L/K)) : ℝ) / Nat.card Gal(L/K))
```

Use B4 for each `L^D/K`, remove ramified primes of `L`, then finite linear
combinations of limits. `Nat.card Gal(L/K) > 0` ensures positive totient and
positive density. This is generator density, not density of each generator.

**W2 — extract a rational generator prime. S–M after W1/D1/D2/H3.
Existing: finite Galois fixed-field correspondence E8.**
For `g : Gal(L/ℚ)`, `H = Subgroup.zpowers g`, `F = IntermediateField.fixedField H`:

```lean
theorem exists_degreeOne_generator (S : Finset (Prime ℚ)) (N : ℕ) :
  ∃ v : Prime F, v ∈ Generators F L ∧ DegreeOne F v ∧ N ≤ norm v ∧
    ∀ u : Prime ℚ, v.asIdeal.under (𝓞 ℚ) = u.asIdeal →
      u ∉ S ∧ Unram ℚ L u
```

Use `Gal(L/F) ≃* H` to install cyclicity. Remove degree-greater-than-one primes
of `F/ℚ`, primes above `S`, and primes above the discriminant divisors of `L`.
This requires the bounded-sum estimate, not any effective bound on the first
prime. `S` may contain primes unrelated to the extension.

**W3 — the weaker finite-monoid theorem. M, capped: no for full assembly.
Existing: E1.**

```lean
theorem powerFrobCover
    {M : Type*} [Monoid M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M)
    (S : Finset (Prime ℚ)) (N : ℕ) : PowerFrobCover f S N
```

Use the image in units, G2, and W2 with the element corresponding to `f g`.
The generator at the selected prime has a nonnegative power equal to that
element (finite group). H3/G4 compare the chosen local Frobenius; lift the
conjugating element through the surjective quotient. Project back to `M`.
No equality `f g = f (σ * QFrob * σ⁻¹)` is claimed without the power.

## A: Deuring reduction and the full admission

For full Chebotarev the cyclic step must prescribe **a particular generator**,
not merely any generator. In `C₅`, for example, all four nonidentity elements
generate the same subgroup and are not conjugate. Subfield zeta functions see
their sum, not four separately labelled prime sets. Thus B4 and W1 alone do
not prove the target, even for a cyclic quotient.

A gives a valid long route. Its missing foundation is ray class theory and
finite-order Hecke L-functions over arbitrary number fields. The following
statements specify the arithmetic obligations rather than disguising them as
available imports. All `Ray*`, `HeckeL`, `ArtinMap` names here are new APIs.
A1–A6 need their own detailed implementation projects before capped dispatch.

**A1 — ray ideal quotient. L, capped: no. Existing: Mathlib fractional ideals;
E20 is only an ordinary-class analogue.**
Define `RayModulus K` as a nonzero integral ideal and a finite set of real
places; `RayIdealGroup K m` as fractional ideals prime to the finite modulus;
`RayPrincipal K m` as principal ideals generated by elements congruent to 1
modulo the finite modulus and positive at its specified real places. Define
`RayClassGroup K m := RayIdealGroup K m ⧸ RayPrincipal K m`. Required interface:

```lean
def rayClass (m : RayModulus K) : RayIdealGroup K m →* RayClassGroup K m
theorem rayClass_surjective (m : RayModulus K) : Function.Surjective (rayClass m)
theorem rayClass_eq_one_iff (a : RayIdealGroup K m) :
  rayClass m a = 1 ↔ a ∈ RayPrincipal K m
```

The quotient lemmas are S once the definitions exist; fractional-ideal
congruence and positivity well-definedness are the L work. Ignoring real
places would silently exclude needed ramified-at-infinity cyclic extensions.

**A2 — ray class finiteness. L, capped: no. Existing: ordinary class-group
finiteness used in E5/E20, finite quotient rings and units.**

```lean
theorem finite_rayClassGroup (m : RayModulus K) : Finite (RayClassGroup K m)
```

Prove the exact-sequence comparison with the ordinary class group, finite
residue units, and signs. The statement is precise; the comparison sequence
has not been located as an existing declaration in this checkout.

**A3 — reciprocity for a given cyclic extension. XL, capped: no. Existing:
E10 supplies prime Frobenius; there is no located global reciprocity theorem.**
For `[IsGalois K L] [IsCyclic Gal(L/K)]`:

```lean
theorem exists_rayClass_artin :
  ∃ (m : RayModulus K) (art : RayClassGroup K m →* Gal(L/K)),
    Function.Surjective art ∧
    ∀ v : Prime K, CoprimeToModulus v m →
      Unram K L v ∧ art (rayPrimeClass m v) = frob K L v
```

`CoprimeToModulus` means coprime to the finite modulus; `rayPrimeClass` is the
class of that prime ideal. Concrete sub-obligations are: the prime Frobenius
map extends multiplicatively to `RayIdealGroup`; it kills `RayPrincipal` for
some modulus (Artin reciprocity); the induced quotient map is surjective.
None may be justified using the Chebotarev theorem being proved. Existence
of every class field is unnecessary; reciprocity for the given extension is
still major missing mathematics.

**A4 — finite-order Hecke Euler products. L, capped: no. Existing: E6's
`Chebotarev.weighted_eulerProduct_eq_tsum`; E19 as the rational analogy.**
For `χ : RayClassGroup K m →* ℂˣ`, define `HeckeLSeries m χ s` by summing over
integral ideals coprime to the finite modulus. Prove, for `1 < s.re`,

```lean
theorem heckeLSeries_eq_eulerProduct (hs : 1 < s.re) :
  HeckeLSeries m χ s =
    ∏' v : {v : Prime K // CoprimeToModulus v m},
      (1 - (χ (rayPrimeClass m v.1) : ℂ) * (norm v.1 : ℂ)^(-s))⁻¹
```

Extend weights by zero at excluded primes and use finite image to prove unit
norm. This avoids reimplementing the unweighted ideal Euler product.

**A5 — continuation near 1. XL, capped: no. Existing: E20 only for `Re s > 1`;
E19 continuation is only over `ℚ`.**

```lean
theorem exists_heckeL_near_one (χ : RayClassGroup K m →* ℂˣ) (hχ : χ ≠ 1) :
  ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
    ∀ s : ℂ, 1 < s.re → F s = HeckeLSeries m χ s
```

One implementation needs ray-class partial-zeta continuation with equal
residues, followed by character cancellation; another needs theta/Mellin
analysis for finite-order Hecke characters. The ordinary-class asymptotics in
E16/E20 do not establish the ray-class continuation. This is a research-scale
leaf with an exact endpoint, not a few-hour proof.

**A6 — nonvanishing at 1. XL, capped: no. Existing: E19 only as a model.**
With the chosen continuation `HeckeL m χ` from A5:

```lean
theorem heckeL_one_ne_zero (χ : RayClassGroup K m →* ℂˣ) (hχ : χ ≠ 1) :
  HeckeL m χ 1 ≠ 0
```

For cyclic-extension characters one can use zeta factorization and the simple
pole after proving holomorphy of all nontrivial factors; for all ray characters,
a general Hecke nonvanishing argument is needed. In either approach A5 cannot
be skipped. Factorization without regularity does not rule out cancelling
zeros and poles. Do not assume the conclusion as a field in a structure.

**A7 — character-weighted prime sums. M–L, capped: no. Existing: E19's
orthogonality/PrimesInAP strategy, A4–A6.**
For finite `H = Gal(L/K)` cyclic and `χ : H →* ℂˣ`, use A3 to view `χ` as a
Hecke character. The precise endpoint, ignoring finitely many bad primes, is

```lean
theorem weighted_frob_primeSum_limit (χ : H →* ℂˣ) :
  Tendsto (fun s : ℝ =>
    (∑' v : {v : Prime K // Unram K L v},
      (χ (frob K L v.1) : ℂ) * (norm v.1 : ℂ)^(-(s : ℂ))) / (ell s : ℂ))
    (𝓝[>] 1) (𝓝 (if χ = 1 then 1 else 0))
```

Required leaves: character orthogonality on finite cyclic groups (S–M),
logarithmic Euler remainder (M, adapt Z3 with complex branch care), and bounded
nontrivial logarithms near 1 using A5/A6 (M). Alternatively use log derivatives
throughout; then the density normalization and all prime weights must change
consistently. Do not mix the two normalizations.

**A8 — exact cyclic class density. S–M after A7; capped: possible.**

```lean
theorem cyclic_exact_frob_density [IsCyclic Gal(L/K)] (a : Gal(L/K)) :
  LogDensity {v : Prime K | Unram K L v ∧ frob K L v = a}
    (1 / (Nat.card Gal(L/K) : ℝ))
```

Fourier inversion isolates `a`, including when it is a specified generator.
This is the step missing from the zeta-only route B.

**A9 — Deuring reduction and wrapper. M, capped: no for all interfaces at once.
Existing: E1/E8; shared D1/D2/H3/G4.**

```lean
theorem exists_rational_frob_class
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (a : Gal(L/ℚ)) (S : Finset (Prime ℚ)) (N : ℕ) :
  ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
    Unram ℚ L hq.toHeightOneSpectrumRingOfIntegersRat ∧
    IsConj a (frob ℚ L hq.toHeightOneSpectrumRingOfIntegersRat)
```

Take `F = L^⟨a⟩`, apply A8 to the specific element `a` viewed in `Gal(L/F)`,
remove higher-degree primes of `F/ℚ` and finite exclusions, then use H3.
Finally realize a surjective finite quotient using G2, compare its chosen local
Frobenius using G4, lift the conjugator, and invoke E1. This discharges the exact
original theorem, including arbitrary `N` and `S`. Quantitative density in the
nonabelian group is not required by its type.

## Other proposed shortcuts and their limits

A direct analytic route B to **full** Chebotarev could develop Artin L-functions,
character induction, and nonvanishing/holomorphy at 1 for the needed induced
characters. It would still need the missing cyclic-character analysis of
A3–A7 (or a separately justified replacement). The Dedekind pole alone gives
permutation-character information invariant under coprime powers. Calling that
information “density in Galois groups” does not strengthen its conclusion.
For this repository, the weak B route above is the useful analytic project;
a second full Artin-L development would add interfaces without helping B5.

Brauer–Nesbitt is not the missing step. E3 already avoids it and works in finite
characteristic without character-theoretic semisimplicity assumptions. Applying
Brauer–Nesbitt would still require extending Frobenius data to enough group
elements. Even topological generation by Frobenius is insufficient: the
property “has a fixed vector” is not closed under products.

The cyclotomic theorem E2 proves the full claim only after a factorization of
`f` through a finite cyclotomic character is supplied. A cyclotomic determinant
does not supply such a factorization for a rank-two representation. Proving
abelianity or triangularity from the B5 hypotheses would itself need new
arithmetic; assuming it would risk assuming the desired reducibility. C instead
works for arbitrary finite images, with no classification of subgroups of
`GL₂(k)` and no characteristic restrictions beyond B5's existing inputs.

There may be other proofs specific to hardly-ramified representations, but no
such Chebotarev-free argument was located in the checked declarations. This
plan does not turn that unsuccessful search into a nonexistence claim.

## Dispatch and acceptance

Start with these three independent bounded leaves:

1. **C1**: public `trace_eq_one_add_det_iff_fixedVector`; 40–100 lines,
   about 2–4 hours, using TraceReducibility's existing matrix calculation.
2. **C2**: `fixedVector_conj_pow`; 20–60 lines, about 1–3 hours,
   an elementary representation calculation.
3. **Z1**: `log_dedekindZeta_asymptotic`; 40–100 lines, about 2–4 hours,
   using the existing positive residue limit and Euler-product positivity.

Next, scope G4 and B1 carefully: the local/global Frobenius and prime-splitting
interfaces are likely to cost more than the final limit algebra. G1 is a useful
small follow-on. C3 can be proved with its explicit power-cover hypothesis,
but it is scaffolding and must not be reported as B5 closed.

Expect the recommended route to require several thousand new Lean lines and
multiple weeks of work across the arithmetic interfaces; it is not one capped
worker's task. The full A route adds substantial ray-class/Hecke foundations,
plausibly months. These are planning ranges, not measured benchmarks.

For each implemented leaf, build its module with this pinned Mathlib, inspect
`#print axioms`, and reject any `sorryAx` or new axiom dependency. For C4, also
check that `not_isIrreducible_of_frobenius_traces` no longer depends on the full
Chebotarev admission. For A9, check the unchanged target type and its axiom list.
No use of an admitted theorem in its own replacement, including through an
intermediate lemma, is acceptable. Existing three-adic/lifting/family admissions
are outside this plan's claim of completion.

Reproduce the inventory checks without modifying the repository:

```bash
git rev-parse HEAD
git -C .lake/packages/mathlib rev-parse HEAD
rg -n 'chebotarev_frobenius_dense|not_isIrreducible_of_frobenius_traces' FLT
rg -n -i 'chebotarev|hecke.character|artin.reciprocity|class.field.theory' \
  .lake/packages/mathlib/Mathlib
cat > /tmp/chebotarev-plan-audit.lean <<'LEAN'
import FLT.GaloisRepresentation.HardlyRamified.B5Inputs
import FLT.AINTLIB.CebotarevDensity.NumberFieldEulerProduct
#print axioms NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT
#print axioms Chebotarev.dedekindZeta_eq_tprod_primeIdeal
#print axioms GaloisRepresentation.B5Inputs.not_isIrreducible_of_trace_eq_one_add_det
#print axioms GaloisRepresentation.B5Inputs.chebotarev_frobenius_dense_of_factors_cyclotomic
#print axioms GaloisRepresentation.B5Inputs.chebotarev_frobenius_dense
LEAN
lake env lean /tmp/chebotarev-plan-audit.lean
```

The negative-name search exits 1 when no match is found; inspect the existing
Dirichlet and Dedekind files separately as documented above. No Lean source was
changed for this plan. Commit locally only; do not push.
