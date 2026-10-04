/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.IntegralThickeningReduction
public import FLT.PadicHodgeTheory.ComplexPadicScalarResidue

/-! # Integral theta and p-power coefficient thickenings -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Both precision directions are imposed before p is inverted. -/
def complexThickeningIdeal (r s : ℕ) : Ideal (Ainf p) :=
  RingHom.ker (complexTheta p) ^ r ⊔ Ideal.span {(p : Ainf p) ^ s}

/-- The actual integral ring modulo theta order r and p order s. -/
abbrev ComplexIntegralThickening (r s : ℕ) := Ainf p ⧸ complexThickeningIdeal p r s

/-- The residue coefficient ring is the actual O_C modulo p^s. -/
abbrev ComplexIntegerModPow (s : ℕ) := 𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ s}

/-- Both precision coordinates give the expected quotient maps. -/
theorem complexThickeningIdeal_antitone {r r' s s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    complexThickeningIdeal p r' s' ≤ complexThickeningIdeal p r s := by
  apply sup_le_sup (Ideal.pow_le_pow_right hr)
  rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
  exact Ideal.pow_le_pow_right hs

/-- Reduce either or both integral precision coordinates. -/
def complexThickeningReduce {r r' s s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    ComplexIntegralThickening p r' s' →+* ComplexIntegralThickening p r s :=
  Ideal.Quotient.factor (complexThickeningIdeal_antitone p hr hs)

/-- Precision reduction is surjective on the actual rings. -/
theorem complexThickeningReduce_surjective {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    Function.Surjective (complexThickeningReduce p hr hs) :=
  Ideal.Quotient.factor_surjective _

/-- The original p-power is zero in the coefficient thickening. -/
theorem complexIntegralThickening_prime_pow (r s : ℕ) :
    (p : ComplexIntegralThickening p r s) ^ s = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _) p, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply (show Ideal.span {(p : Ainf p) ^ s} ≤ complexThickeningIdeal p r s from le_sup_right)
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Theta modulo p^s has exactly the first-order defining ideal as kernel. -/
theorem complexTheta_modPow_ker (s : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ s})).comp
      (complexTheta p)) = complexThickeningIdeal p 1 s := by
  have hm : (Ideal.span {(p : Ainf p) ^ s}).map (complexTheta p) =
      Ideal.span {(p : 𝓞_ℂ_[p]) ^ s} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  rw [← hm, integralReduction_ker _ (complexTheta_surjective p)]
  simp only [complexThickeningIdeal, pow_one, sup_comm]

/-- Theta descends to every positive integral theta order. -/
def complexThickeningTheta (r s : ℕ) (hr : 0 < r) :
    ComplexIntegralThickening p r s →+* ComplexIntegerModPow p s :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (complexTheta p)) (by
      change complexThickeningIdeal p r s ≤ RingHom.ker _
      rw [complexTheta_modPow_ker]
      exact complexThickeningIdeal_antitone p hr le_rfl)

/-- The descended theta is surjective, by the original integral theta surjectivity. -/
theorem complexThickeningTheta_surjective (r s : ℕ) (hr : 0 < r) :
    Function.Surjective (complexThickeningTheta p r s hr) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _
    (Ideal.Quotient.mk_surjective.comp (complexTheta_surjective p))

/-- Its entire kernel is the image of the original theta kernel. -/
theorem complexThickeningTheta_ker (r s : ℕ) (hr : 0 < r) :
    RingHom.ker (complexThickeningTheta p r s hr) =
      (RingHom.ker (complexTheta p)).map (Ideal.Quotient.mk (complexThickeningIdeal p r s)) := by
  rw [complexThickeningTheta, Ideal.ker_quotient_lift, complexTheta_modPow_ker]
  have hz : (Ideal.span {(p : Ainf p) ^ s}).map
      (Ideal.Quotient.mk (complexThickeningIdeal p r s)) = ⊥ :=
    Ideal.map_mk_eq_bot_of_le le_sup_right
  change (RingHom.ker (complexTheta p) ^ 1 ⊔ Ideal.span {(p : Ainf p) ^ s}).map _ = _
  rw [pow_one, Ideal.map_sup, hz, sup_bot_eq]

/-- Order r gives an explicitly r-nilpotent reduction kernel. -/
theorem complexThickeningTheta_ker_pow (r s : ℕ) (hr : 0 < r) :
    RingHom.ker (complexThickeningTheta p r s hr) ^ r = ⊥ := by
  rw [complexThickeningTheta_ker p r s hr, ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le le_sup_left

end PadicHodgeTheory
