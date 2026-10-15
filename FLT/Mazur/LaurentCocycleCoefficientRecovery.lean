/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentScaledEvaluationCoefficients
public import Mathlib.Tactic.LinearCombination

/-!
# Recovering a Laurent cocycle from one coefficient

The coefficient of the third variable at exponent one in the multiplicative
cocycle equation expresses the full error as a coboundary of its own outer
coefficient at exponent one. This calculation works in every characteristic.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentCocycleCoefficientRecovery
open LaurentPolynomial PolygonChartScaling LaurentPairNaturality
open LaurentScaledEvaluationCoefficients PolygonScalingNaturality
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Evaluation at the two independent universal units retains the whole Laurent polynomial. -/
theorem pairEval₂_universal :
    pairEval₂ ((C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]).comp C)
      (Units.map (C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]) (coordinateUnit (1 : Rˣ)))
      (coordinateUnit (1 : R[T;T⁻¹]ˣ)) = RingHom.id _ := by
  have he : eval₂ ((C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]).comp C)
      (Units.map (C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]) (coordinateUnit (1 : Rˣ))) = C := by
    apply ringHom_ext <;> simp [eval₂_C, eval₂_T, coordinateUnit]
  unfold pairEval₂
  rw [he]
  exact laurent_one

/-- Extract one coefficient after evaluating the first variable at a constant unit. -/
theorem pair_scaled_coeff (f : R →+* S) (u v : Sˣ) (p : R[T;T⁻¹][T;T⁻¹]) (d : ℤ) :
    (pairEval₂ (C.comp f) (Units.map (C : S →+* S[T;T⁻¹]) u)
      (coordinateUnit v) p).coeff d = eval₂ f u (p.coeff d) * (v ^ d).val := by
  unfold pairEval₂
  have he : eval₂ (C.comp f) (Units.map (C : S →+* S[T;T⁻¹]) u) =
      C.comp (eval₂ f u) := (eval₂_map f (C : S →+* S[T;T⁻¹]) u).symm
  rw [he]
  exact eval₂_scaled_coeff (eval₂ f u) v p d

/-- The third-variable coefficient at one reconstructs the full evaluated two-variable cocycle. -/
theorem cocycle_recovery (f : R →+* S) (p : R[T;T⁻¹][T;T⁻¹]) (u v : Sˣ)
    (hc : ∀ x y z : S[T;T⁻¹]ˣ,
      z.val * pairEval₂ (C.comp f) x y p + pairEval₂ (C.comp f) (x * y) z p =
        x.val * pairEval₂ (C.comp f) y z p + pairEval₂ (C.comp f) x (y * z) p) :
    pairEval₂ f u v p = u.val * eval₂ f v (p.coeff 1) +
      v.val * eval₂ f u (p.coeff 1) - eval₂ f (u * v) (p.coeff 1) := by
  let U : Sˣ → S[T;T⁻¹]ˣ := Units.map (C : S →+* S[T;T⁻¹])
  have ha := hc (U u) (U v) (coordinateUnit 1)
  have hU : U u * U v = U (u * v) := (map_mul _ u v).symm
  have hv : U v * coordinateUnit 1 = coordinateUnit v := (coordinate_factor v).symm
  rw [hU, hv] at ha
  have he : pairEval₂ (C.comp f) (U u) (U v) p = C (pairEval₂ f u v p) :=
    (congrArg (fun F : R[T;T⁻¹][T;T⁻¹] →+* S[T;T⁻¹] ↦ F p)
      (pairEval₂_map f C u v)).symm
  rw [he] at ha
  have hh := congrArg (fun P : S[T;T⁻¹] ↦ P.coeff 1) ha
  have hz : (coordinateUnit (1 : Sˣ)).val = (T 1 : S[T;T⁻¹]) := by
    simp [coordinateUnit]
  have hu : (U u).val = C u.val := rfl
  rw [hz, hu, mul_comm (T 1)] at hh
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← smul_eq_C_mul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, T_apply, ite_true,
    mul_one, U, pair_scaled_coeff, Units.val_one, zpow_one] at hh
  linear_combination hh

end FLT.Mazur.LaurentCocycleCoefficientRecovery
