/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCorrectionPunctures

/-!
# Reduction of the complete arithmetic puncture factors

Both direct and reflected substitutions are the identity modulo the parameter.
This keeps the full inverse compensation rather than a truncated coordinate.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- Every value of either full correction differs from its input in the parameter ideal. -/
theorem correctionPunctureFactor_sub_mem (m : ℕ) (t : Quotient R π m)
    (q : R[T;T⁻¹]) (b : Bool) (z : (Quotient R π m)[T;T⁻¹]) :
    correctionPunctureFactor R π m t q b z - z ∈
      (ideal (Quotient R π m) (parameter R π m)).map
        (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹]) := by
  cases b
  · exact LaurentNearIdentityAutomorphism.eval_sub_mem _ _
      (nilpotentShearRightUnit_sub_mem _ _ _ _ _) z
  · exact LaurentNearIdentityAutomorphism.eval_sub_mem _ _
      (nilpotentShearLeftUnit_sub_mem _ _ _ _) z

/-- At arithmetic layer zero both complete puncture corrections are the identity. -/
theorem correctionPunctureFactor_zero (t : Quotient R π 0) (q : R[T;T⁻¹]) (b : Bool) :
    correctionPunctureFactor R π 0 t q b = AlgEquiv.refl := by
  ext z : 1
  have h := correctionPunctureFactor_sub_mem R π 0 t q b z
  have hp : parameter R π 0 = 0 := by
    simpa only [Nat.zero_add, pow_one] using parameter_pow R π 0
  simpa only [hp, ideal, Ideal.span_singleton_zero, Ideal.map_bot,
    Submodule.mem_bot, sub_eq_zero, AlgEquiv.coe_refl, id_eq] using h

/-- Both full branches of a paired node also reduce to the identity at layer zero. -/
theorem twoBranchCorrectionPunctureFactor_zero (t : Quotient R π 0)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    twoBranchCorrectionPunctureFactor R π 0 t q b = AlgEquiv.refl := by
  rw [twoBranchCorrectionPunctureFactor,
    correctionPunctureFactor_zero, correctionPunctureFactor_zero]
  rfl

end FLT.Mazur.PolygonArithmeticStages
