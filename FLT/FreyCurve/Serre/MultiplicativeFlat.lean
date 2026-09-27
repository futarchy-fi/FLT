/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.TwistFlat

/-!
# Finite-flat torsion at multiplicative reduction

Divisibility of the Tate parameter valuation gives a quadratic Kummer model,
whether or not multiplicative reduction is split.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

open scoped TensorProduct WeierstrassCurve.Affine
open ValuativeRel Polynomial

namespace WeierstrassCurve

universe v
variable {K : Type v} [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K] [DecidableEq (AlgebraicClosure K)]

/-- Multiplicative torsion with divisible parameter valuation has a twisted Kummer comparison. -/
theorem exists_twistModel_comparison_of_multiplicative_valuation
    (A : ValuationSubring K) [IsDiscreteValuationRing A]
    (hA : A.toSubring = (𝒪[K] : Subring K)) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasMultiplicativeReduction A]
    (m : ℕ) (hm : 0 < m) [NeZero m] (b : Kˣ)
    (hb : (valuation K E.j)⁻¹ = valuation K (b : K) ^ m) :
    ∃ (u d : Aˣ) (r : A) (hr : 2 * r = 1),
      let := KummerAlgebra.twistHopfAlgebra A m u d r hr
      ∃ f : Additive (K ⊗[A] KummerAlgebra.twistModel A m u d →ₐ[K]
          AlgebraicClosure K) →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K]
          (E.galoisRep m hm).Space, Function.Bijective f := by
  let Ω := AlgebraicClosure K
  obtain ⟨t, c, hD, hs⟩ := E.exists_split_twist_parameters (R := A)
  obtain ⟨d, hd⟩ := hD
  obtain ⟨r, hr⟩ := h2.exists_right_inv
  let E' := E.quadraticTwistOf (algebraMap A K t) (algebraMap A K c)
  have hDk : (algebraMap A K t) ^ 2 - 4 * algebraMap A K c ≠ 0 := by
    simpa only [map_sub, map_pow, map_mul, map_ofNat, hd] using
      (d.isUnit.map (algebraMap A K)).ne_zero
  let : E'.IsElliptic := E.isElliptic_quadraticTwistOf _ _ hDk
  let hsplit : E'.HasSplitMultiplicativeReduction A := by
    rwa [E.baseChange_integralModel_quadraticTwistOf A t c] at hs
  let : E'.HasSplitMultiplicativeReduction 𝒪[K] := by
    have transport (B C : Subring K) [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
        [IsFractionRing B K] [IsFractionRing C K] (h : B = C) :
        E'.HasSplitMultiplicativeReduction B → E'.HasSplitMultiplicativeReduction C := by
      subst C
      exact id
    let : IsDiscreteValuationRing A.toSubring := inferInstanceAs (IsDiscreteValuationRing A)
    let : IsFractionRing A.toSubring K := inferInstanceAs (IsFractionRing A K)
    exact transport A.toSubring 𝒪[K] hA
      hsplit
  have he : A.valuation.IsEquiv (valuation K) := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [A.valuation_le_one_iff]
    change x ∈ A.toSubring ↔ x ∈ (𝒪[K] : Subring K)
    rw [hA]
  have hq : valuation K (E'.qUnit : K) = valuation K ((b : K) ^ m) := by
    change valuation K (tateParameter E'.j) = _
    rw [valuation_tateParameter_eq E'.one_lt_valuation_j, map_pow,
      E.j_quadraticTwistOf _ _ inferInstance, hb]
  have hval := he.eq_iff.mpr hq
  rw [map_pow] at hval
  obtain ⟨u, hu⟩ := A.exists_unit_factor_of_valuation_eq_pow m E'.qUnit b hval
  let tΩ := algebraMap K Ω (algebraMap A K t)
  let cΩ := algebraMap K Ω (algebraMap A K c)
  let f : Polynomial Ω := X ^ 2 - C tΩ * X + C cΩ
  have hf : f.degree = 2 := by
    simpa [f, sub_eq_add_neg] using
      (degree_quadratic (b := -tΩ) (c := cΩ) (one_ne_zero : (1 : Ω) ≠ 0))
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root f (by rw [hf]; decide)
  have hx' : x ^ 2 - tΩ * x + cΩ = 0 := by simpa [f, IsRoot] using hx
  have hw : tΩ - 2 * x ≠ 0 := by
    have heq : (tΩ - 2 * x) ^ 2 = tΩ ^ 2 - 4 * cΩ := by
      linear_combination 4 * hx'
    have hDΩ : tΩ ^ 2 - 4 * cΩ ≠ 0 := by
      simpa [tΩ, cΩ, map_ofNat] using ((map_ne_zero (algebraMap K Ω)).mpr hDk)
    exact fun h ↦ hDΩ (by rw [← heq, h, zero_pow (by decide)])
  refine ⟨u, d, r, hr, ?_⟩
  exact E.twistModel_comparison_of_root t c d hd m hm u r hr b hu x hx' hw

end WeierstrassCurve
