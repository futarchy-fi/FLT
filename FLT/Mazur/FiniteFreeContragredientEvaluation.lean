/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeContragredient
public import FLT.Mazur.ProjectiveLinearSubstitution

/-!
# Evaluation of dual homogeneous generators on sections

Evaluation of the actual polynomial substitution defining the dual projective
transition sends a section vector to its original coordinate transport. Thus
the inverse-transpose convention is determined on all homogeneous polynomials,
not just asserted for projective points.
-/

@[expose] public noncomputable section
open MvPolynomial
universe u
namespace FLT.Mazur.FiniteFreeContragredient
open ProjectiveSpace
variable {R : Type u} [CommRing R] {ι κ : Type u} [Finite ι] [Finite κ]

/-- Evaluating a linear polynomial is the actual dual pairing with the section vector. -/
lemma evaluate_linearForm (w v : ι →₀ R) :
    aeval (fun i ↦ v i) (linearForm w) = dualCoordinates R ι w v := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, LinearMap.add_apply, hw, hz]
  | single i r => simp [dualCoordinates_single_left]

/-- Pulling back a dual generator evaluates to the transported section coordinate. -/
lemma evaluate_inverse_generator (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (v : ι →₀ R) (j : κ) :
    aeval (fun i ↦ v i) (linearForm ((map e).symm (Finsupp.single j 1))) = e v j := by
  rw [evaluate_linearForm]
  have h := pairing e ((map e).symm (Finsupp.single j 1)) v
  simpa only [LinearEquiv.apply_symm_apply, dualCoordinates_single_left, one_mul] using h.symm

/-- The polynomial pullback in the dual convention evaluates by original section transport. -/
lemma evaluate_contragredient (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v : ι →₀ R) :
    (aeval (fun i ↦ v i)).comp (linearSubstitution (map e).symm.toLinearMap) =
      aeval (fun j ↦ e v j) := by
  ext j
  simp only [AlgHom.comp_apply, linearSubstitution_X, aeval_X]
  exact evaluate_inverse_generator e v j

/-- The evaluation formula holds for every homogeneous numerator, of any degree. -/
lemma evaluate_contragredient_apply (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v : ι →₀ R)
    (p : MvPolynomial κ R) :
    aeval (fun i ↦ v i) (linearSubstitution (map e).symm.toLinearMap p) =
      aeval (fun j ↦ e v j) p :=
  DFunLike.congr_fun (evaluate_contragredient e v) p

end FLT.Mazur.FiniteFreeContragredient
