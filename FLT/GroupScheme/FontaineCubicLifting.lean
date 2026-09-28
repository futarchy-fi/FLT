/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineCubicNewton
public import FLT.GroupScheme.FontainePointSeparation
public import FLT.Mathlib.Analysis.Normed.Field.CubicHensel
public import FLT.Mathlib.RingTheory.PowerBasisApproximateRoots

/-!
# Compatible integral lifting for cubic presentations

For a monogenic algebra whose differentials are killed by three and whose
defining polynomial is `X³ + aX + b`, every approximate point of precision
`m > 3/2` lifts to an integral point agreeing at precision `m - 1`.
The cubic presentation is an explicit restriction, not a claim about arbitrary
finite flat models.
-/

@[expose] public noncomputable section

open Polynomial

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- The cubic Hensel radius is less than one, and its square is less than
the norm of three, exactly when the original precision exceeds three halves. -/
theorem cubic_hensel_radius_bounds {m : ℚ} (hm : 3 / 2 < m) :
    (3 : ℝ) ^ (-((m - 1 : ℚ) : ℝ)) < 1 ∧
      ((3 : ℝ) ^ (-((m - 1 : ℚ) : ℝ))) ^ 2 < (3 : ℝ)⁻¹ := by
  have hm' : (3 / 2 : ℝ) < (m : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hm
  constructor
  · apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    push_cast
    linarith
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_neg_one]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    push_cast
    linarith

/-- An approximate cubic root with derivative valuation at most one lifts
to an integral root, retaining precision `m - 1` for every `m > 3/2`. -/
theorem exists_integral_cubic_root (a b : ℤ_[3])
    (x : ThreeAdicIntegers E) {m : ℚ} (hm : 3 / 2 < m)
    (hx : aeval x (X ^ 3 + C a * X + C b) ∈ threeAdicValuationIdeal E m)
    (hd : (3 : ℝ)⁻¹ ≤ spectralNorm ℚ_[3] E
      (aeval (x : E) (X ^ 3 + C a * X + C b).derivative)) :
    ∃ y : ThreeAdicIntegers E,
      y - x ∈ threeAdicValuationIdeal E (m - 1) ∧
      aeval y (X ^ 3 + C a * X + C b) = 0 := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  let ρ := (3 : ℝ) ^ (-((m - 1 : ℚ) : ℝ))
  have hρ : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  obtain ⟨hρ1, hρ2⟩ := cubic_hensel_radius_bounds hm
  have hx1 : ‖(x : E)‖ ≤ 1 := (isIntegral_iff_spectralNorm_le_one E _).mp x.property
  have hder : aeval (x : E) (X ^ 3 + C a * X + C b).derivative =
      3 * (x : E) ^ 2 + algebraMap ℤ_[3] E a := by
    simp only [derivative_X_pow, derivative_mul, derivative_C,
      derivative_X, zero_mul, mul_one, zero_add, add_zero, map_add, map_mul,
      map_pow, aeval_X, aeval_C]
    norm_num only [Nat.add_one_sub_one]
    erw [map_ofNat]
  rw [hder] at hd
  change (3 : ℝ)⁻¹ ≤ ‖3 * (x : E) ^ 2 + algebraMap ℤ_[3] E a‖ at hd
  have heval : aeval (x : E) (X ^ 3 + C a * X + C b) =
      ((aeval x (X ^ 3 + C a * X + C b) : ThreeAdicIntegers E) : E) :=
    aeval_algHom_apply (ThreeAdicIntegers E).val x _
  have hf : ‖(x : E) ^ 3 + algebraMap ℤ_[3] E a * x + algebraMap ℤ_[3] E b‖ ≤
      ρ * ‖3 * (x : E) ^ 2 + algebraMap ℤ_[3] E a‖ := by
    have he : ‖(x : E) ^ 3 + algebraMap ℤ_[3] E a * x + algebraMap ℤ_[3] E b‖ ≤
        (3 : ℝ) ^ (-(m : ℝ)) := by
      change spectralNorm ℚ_[3] E
        ((x : E) ^ 3 + algebraMap ℤ_[3] E a * x + algebraMap ℤ_[3] E b) ≤ _
      simpa only [map_add, map_mul, map_pow, aeval_X, aeval_C] using
        (heval ▸ hx : spectralNorm ℚ_[3] E
          (aeval (x : E) (X ^ 3 + C a * X + C b)) ≤ (3 : ℝ) ^ (-(m : ℝ)))
    apply he.trans
    calc
      (3 : ℝ) ^ (-(m : ℝ)) = ρ * (3 : ℝ)⁻¹ := by
        dsimp only [ρ]
        rw [← Real.rpow_neg_one, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        push_cast
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hρ
  have hna : IsNonarchimedean (norm : E → ℝ) := isNonarchimedean_spectralNorm
  have h3 : ‖(3 : E)‖ = (3 : ℝ)⁻¹ := spectralNorm_three E
  obtain ⟨y, hy, hroot⟩ := hna.exists_root_cubic_of_norm_bounds
    (algebraMap ℤ_[3] E a) (algebraMap ℤ_[3] E b) (x : E) hρ hx1 hf
    (by rw [h3]; exact (mul_lt_of_lt_one_right (by norm_num) hρ1).trans_le hd)
    (hρ2.trans_le hd)
  have hy1 : ‖y‖ ≤ 1 := by
    have hn := hna (y - x) x
    rw [sub_add_cancel] at hn
    exact hn.trans (max_le (hy.trans hρ1.le) hx1)
  let yO : ThreeAdicIntegers E := ⟨y, (isIntegral_iff_spectralNorm_le_one E y).mpr hy1⟩
  refine ⟨yO, hy, ?_⟩
  apply Subtype.ext
  have he : aeval (yO : E) (X ^ 3 + C a * X + C b) =
      ((aeval yO (X ^ 3 + C a * X + C b) : ThreeAdicIntegers E) : E) :=
    aeval_algHom_apply (ThreeAdicIntegers E).val yO _
  change ((aeval yO (X ^ 3 + C a * X + C b) : ThreeAdicIntegers E) : E) = 0
  rw [← he]
  simpa only [map_add, map_mul, map_pow, aeval_X, aeval_C] using hroot

/-- Every approximate point of a differential-annihilated cubic power-basis
algebra lifts integrally after losing one unit of valuation precision. -/
theorem _root_.PowerBasis.exists_cubic_lift_of_three_smul
    {A : Type*} [CommRing A] [Algebra ℤ_[3] A] (pb : PowerBasis ℤ_[3] A)
    (hΩ : ∀ ω : KaehlerDifferential ℤ_[3] A, (3 : ℤ_[3]) • ω = 0)
    (a b : ℤ_[3]) (hf : minpoly ℤ_[3] pb.gen = X ^ 3 + C a * X + C b)
    {m : ℚ} (hm : 3 / 2 < m)
    (u : A →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) :
    ∃ v : A →ₐ[ℤ_[3]] ThreeAdicIntegers E,
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
        (Ideal.Quotient.factorₐ ℤ_[3]
          (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp u := by
  obtain ⟨x, hxu⟩ := Ideal.Quotient.mk_surjective (u pb.gen)
  have hx : aeval x (minpoly ℤ_[3] pb.gen) ∈ threeAdicValuationIdeal E m := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E m))
      (aeval x (minpoly ℤ_[3] pb.gen)) = 0
    rw [← aeval_algHom_apply]
    change aeval (Ideal.Quotient.mk (threeAdicValuationIdeal E m) x)
      (minpoly ℤ_[3] pb.gen) = 0
    rw [hxu, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hd := pb.spectralNorm_derivative_ge_of_three_smul E hΩ x (by linarith) hx
  rw [hf] at hx hd
  obtain ⟨y, hy, hroot⟩ := exists_integral_cubic_root E a b x hm hx hd
  have hyroot : aeval y (minpoly ℤ_[3] pb.gen) = 0 := by rw [hf]; exact hroot
  refine ⟨pb.lift y hyroot, pb.algHom_ext ?_⟩
  simp only [AlgHom.comp_apply, PowerBasis.lift_gen, Ideal.Quotient.mkₐ_eq_mk]
  rw [← hxu]
  exact Ideal.Quotient.eq.mpr hy

/-- Fontaine lifting existence for a killed-by-three model equipped with
a depressed cubic power-basis presentation. -/
theorem FF.exists_cubic_integralPoint_lift (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (pb : PowerBasis ℤ_[3] M.CoordinateRing) (a b : ℤ_[3])
    (hf : minpoly ℤ_[3] pb.gen = X ^ 3 + C a * X + C b)
    {m : ℚ} (hm : 3 / 2 < m)
    (u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) :
    ∃ v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E,
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
        (Ideal.Quotient.factorₐ ℤ_[3]
          (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp u :=
  pb.exists_cubic_lift_of_three_smul E (M.three_smul_kaehlerDifferential_eq_zero hM)
    a b hf hm u

/-- The compatible cubic lift is unique by separation of killed-by-three points. -/
theorem FF.existsUnique_cubic_integralPoint_lift (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (pb : PowerBasis ℤ_[3] M.CoordinateRing) (a b : ℤ_[3])
    (hf : minpoly ℤ_[3] pb.gen = X ^ 3 + C a * X + C b)
    {m : ℚ} (hm : 3 / 2 < m)
    (u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) :
    ∃! v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E,
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
        (Ideal.Quotient.factorₐ ℤ_[3]
          (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp u := by
  obtain ⟨v, hv⟩ := M.exists_cubic_integralPoint_lift E hM pb a b hf hm u
  refine ⟨v, hv, fun w hw ↦ ?_⟩
  exact M.integralPoint_reduction_injective E hM (by linarith) (hw.trans hv.symm)

end ThreeAdicPlan
