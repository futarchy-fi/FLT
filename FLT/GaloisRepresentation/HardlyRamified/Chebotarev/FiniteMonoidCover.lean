/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FiniteGaloisRealization
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.PowerFrobCover
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.TowerDegreeOne
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.W2Statement

/-!
# Power-Frobenius covers of finite monoids

Leaf W3 of `docs/CHEBOTAREV_PLAN.md`: pass through the image in units to a
finite Galois extension, then assemble the power and Frobenius comparisons.
`powerFrobCover` takes `W2Statement.{0}` as its sole arithmetic hypothesis;
W2 itself is a separate leaf. Universe zero suffices because G2 realizes the
quotient inside `AlgebraicClosure ℚ`, while the finite monoid is universe-polymorphic.
-/

@[expose] public section

open NumberField
open GaloisRepresentation.B5Inputs

namespace GaloisRepresentation.Chebotarev

/-- A continuous map to a finite discrete monoid factors through a finite
Galois extension, by applying G2 to its image in the group of units. -/
@[nolint unusedArguments]
theorem exists_finiteGalois_monoid_factorization
    {M : Type*} [Monoid M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L)
      (p : Gal(L/ℚ) →* M),
      ∀ g, p (AlgEquiv.restrictNormalHom L g) = f g := by
  let u := f.toMonoidHom.toHomUnits
  have hu : Continuous u := Units.continuous_iff.mpr
    ⟨f.continuous, f.continuous.comp continuous_inv⟩
  let π : Field.absoluteGaloisGroup ℚ →ₜ* u.range :=
    { u.rangeRestrict with continuous_toFun := hu.subtype_mk _ }
  let ι : u.range →* M := (Units.coeHom M).comp u.range.subtype
  obtain ⟨L, hfin, hgal, e, he⟩ :=
    exists_finiteGalois_realization π u.rangeRestrict_surjective
  exact ⟨L, hfin, hgal, ι.comp e.toMonoidHom, fun g ↦ congrArg ι (he g)⟩

/-- A generator of the automorphism group over the fixed field of `⟨g⟩`
has a nonnegative power whose restriction of scalars is `g`. -/
theorem exists_pow_restrictScalars_eq
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] (g : Gal(L/ℚ))
    (a : Gal(L/IntermediateField.fixedField (Subgroup.zpowers g)))
    (ha : Subgroup.zpowers a = ⊤) :
    ∃ n : ℕ, (AlgEquiv.restrictScalarsHom ℚ a) ^ n = g := by
  let H := Subgroup.zpowers g
  let g' := IntermediateField.subgroupEquivAlgEquiv H ⟨g, Subgroup.mem_zpowers g⟩
  have hg' : g' ∈ Subgroup.zpowers a := ha ▸ Subgroup.mem_top g'
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff g' a).mp
    (mem_powers_iff_mem_zpowers.mpr hg')
  refine ⟨n, ?_⟩
  have h := congrArg (AlgEquiv.restrictScalarsHom ℚ) hn
  rw [map_pow] at h
  exact h

/-- W2 and the degree-one/local Frobenius comparisons give a power of the
chosen rational Frobenius conjugate to any finite Galois automorphism. -/
theorem exists_isConj_pow_restrict_QFrob (hW2 : W2Statement.{0})
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (g : Gal(L/ℚ)) (S : Finset (Prime ℚ)) (N : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
      ∃ n : ℕ, IsConj ((AlgEquiv.restrictNormalHom L (QFrob q hq)) ^ n) g := by
  let F := IntermediateField.fixedField (Subgroup.zpowers g)
  obtain ⟨v, ⟨_, hgen⟩, hq, hN, hv⟩ := hW2 L g S N
  obtain ⟨hS, hu⟩ := hv hq.toHeightOneSpectrumRingOfIntegersRat
    (under_eq_rationalPrime_of_absNorm_eq F v _ hq rfl)
  have hf := hasFrob_tower_degreeOne F L v _ hq rfl (frob F L v)
    ⟨primeAbove F L v, primeAbove_under F L v, isArithFrobAt_frob F L v⟩
  have hc := (isConj_restrict_QFrob_frob L _ hq hu).trans
    (isConj_frob_of_hasFrob ℚ L _ hu _ hf).symm
  obtain ⟨n, hn⟩ := exists_pow_restrictScalars_eq L g (frob F L v) hgen
  refine ⟨v.asIdeal.absNorm, hq, hN, hS, n, ?_⟩
  simpa only [hn] using hc.pow n

/-- Lift the finite conjugator to the absolute Galois group. -/
theorem exists_restrict_eq_conj_pow_QFrob (hW2 : W2Statement.{0})
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (g : Field.absoluteGaloisGroup ℚ) (S : Finset (Prime ℚ)) (N : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
      ∃ (σ : Field.absoluteGaloisGroup ℚ) (n : ℕ),
        AlgEquiv.restrictNormalHom L g =
          AlgEquiv.restrictNormalHom L (σ * (QFrob q hq) ^ n * σ⁻¹) := by
  obtain ⟨q, hq, hN, hS, n, hn⟩ :=
    exists_isConj_pow_restrict_QFrob hW2 L (AlgEquiv.restrictNormalHom L g) S N
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hn
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) τ
  refine ⟨q, hq, hN, hS, σ, n, ?_⟩
  rw [map_mul, map_mul, map_pow, map_inv, hσ]
  exact hτ.symm

end GaloisRepresentation.Chebotarev

namespace GaloisRepresentation.B5Inputs

open GaloisRepresentation.Chebotarev

/-- W3, conditional only on W2: every element of a finite monoid image is a
conjugate of a nonnegative power of a chosen rational Frobenius, outside any
finite excluded set and above any prescribed lower bound. -/
@[nolint unusedArguments]
theorem powerFrobCover (hW2 : W2Statement.{0})
    {M : Type*} [Monoid M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M)
    (S : Finset (Prime ℚ)) (N : ℕ) : PowerFrobCover f S N := by
  obtain ⟨L, hfin, hgal, p, hp⟩ := exists_finiteGalois_monoid_factorization f
  let := hfin
  let := hgal
  intro g
  obtain ⟨q, hq, hN, hS, σ, n, h⟩ := exists_restrict_eq_conj_pow_QFrob hW2 L g S N
  refine ⟨q, hq, hN, hS, σ, n, ?_⟩
  rw [← hp g, ← hp (σ * (QFrob q hq) ^ n * σ⁻¹), h]

end GaloisRepresentation.B5Inputs
