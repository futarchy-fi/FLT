/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.KummerInertia
public import FLT.FreyCurve.Serre.MultiplicativeReduction

/-!
# Trivial inertia on multiplicative torsion

Divisibility of the Tate parameter valuation by the torsion order makes the
whole torsion module unramified. The nonsplit case uses an inertia-equivariant
quadratic twist preserving the j-invariant.
-/

@[expose] public section

open ValuativeRel
open scoped WeierstrassCurve.Affine

namespace ValuationSubring

/-- Agreement of integer rings identifies the valuations on the base field. -/
theorem isEquiv_comap_of_integerRing {K Ω : Type*} [Field K] [ValuativeRel K]
    [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap 𝒪[K] K).range) :
    (A.valuation.comap (algebraMap K Ω)).IsEquiv (ValuativeRel.valuation K) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  change A.valuation (algebraMap K Ω x) ≤ 1 ↔ ValuativeRel.valuation K x ≤ 1
  rw [A.valuation_le_one_iff]
  change x ∈ (A.comap (algebraMap K Ω)).toSubring ↔ x ∈ 𝒪[K]
  rw [hA]
  change (∃ y : 𝒪[K], (y : K) = x) ↔ x ∈ 𝒪[K]
  exact ⟨by rintro ⟨y, rfl⟩; exact y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

end ValuationSubring

namespace WeierstrassCurve

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [DecidableEq Ω]

set_option backward.isDefEq.respectTransparency false in
/-- Inertia fixes all split multiplicative torsion if the Tate parameter valuation
is an `n`-th power in the base value group. -/
theorem inertia_fixes_torsion_of_split_multiplicative
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]
    [IsSepClosed Ω] [Algebra.IsSeparable K Ω]
    (A : ValuationSubring Ω)
    (hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap 𝒪[K] K).range)
    {n : ℕ} (hn : IsUnit (n : A)) (b : Kˣ)
    (hb : (valuation K E.j)⁻¹ = valuation K (b : K) ^ n)
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    (P : (E⁄Ω).Point) (hP : n • P = 0) :
    Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom P = P := by
  obtain ⟨x, m, rfl, hx⟩ := E.exists_tatePoint_of_nsmul_eq_zero Ω P hP
  rw [E.tatePoint_galois]
  congr 1
  apply Units.ext
  apply A.inertia_fixes_of_pow_eq_zpow hn σ hσ E.qUnit b _ x m
    (by simpa [qUnitSepClosure, Units.map] using congrArg Units.val hx)
  have hq : valuation K (E.qUnit : K) = valuation K ((b : K) ^ n) := by
    change valuation K (tateParameter E.j) = _
    rw [valuation_tateParameter_eq E.one_lt_valuation_j, map_pow, hb]
  have heq := (A.isEquiv_comap_of_integerRing hA).eq_iff.mpr hq
  simpa only [Valuation.comap_apply, map_pow] using heq

/-- The same valuation criterion kills all inertia on nonsplit multiplicative torsion. -/
theorem inertia_fixes_torsion_of_multiplicative [CharZero K] [IsAlgClosure K Ω]
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasMultiplicativeReduction 𝒪[K]]
    (A : ValuationSubring Ω)
    (hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap 𝒪[K] K).range)
    {n : ℕ} (hn : IsUnit (n : A)) (b : Kˣ)
    (hb : (valuation K E.j)⁻¹ = valuation K (b : K) ^ n)
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    (P : (E⁄Ω).Point) (hP : n • P = 0) :
    Affine.Point.map (σ : Ω ≃ₐ[K] Ω).toAlgHom P = P := by
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨E', hell, hsplit, e, hj, he⟩ :=
    E.exists_uniform_inertia_equivariant_split_twist_with_j A hA
  let := hell
  let := hsplit
  apply e.injective
  rw [he σ hσ]
  exact E'.inertia_fixes_torsion_of_split_multiplicative A hA hn b (hj ▸ hb) σ hσ (e P)
    (by rw [← map_nsmul, hP, map_zero])

end WeierstrassCurve
