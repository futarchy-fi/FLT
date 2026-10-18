/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormallySmoothStages
public import FLT.Mazur.AdicPositiveAffineLift

/-!
# Actual complete-base lifts of formally smooth affine points

The constructed infinitesimal tower gives an algebra map into the completion.
Completeness of the original base returns an actual point over that same base,
with its original quotient point and every constructed finite lift retained.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicFormallySmoothLift
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open AdicFormallySmoothStages
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (I : Ideal R) [Algebra.FormallySmooth R B] (f : B →ₐ[R] R ⧸ I ^ 1)

/-- The constructed compatible tower as a map to the actual completed coefficient ring. -/
def completed : B →ₐ[R] AdicCompletion I R where
  toRingHom := AdicPositiveAffineLift.liftHom I (fun m ↦ (stage I f m).toRingHom)
    (restriction_stage_apply I f)
  commutes' r := by
    change AdicPositiveAffineLift.liftHom I (fun m ↦ (stage I f m).toRingHom)
      (restriction_stage_apply I f) (algebraMap R B r) = algebraMap R _ r
    apply (AdicCompletionPositiveLimit.equivalence I).injective
    apply Subtype.ext
    funext m
    change AdicCompletion.evalₐ I (m + 1) _ = AdicCompletion.evalₐ I (m + 1) _
    rw [AdicPositiveAffineLift.eval_liftHom, AlgHom.commutes]
    exact (stage I f m).commutes r

/-- The completed point retains the entire constructed map at every positive order. -/
theorem eval_completed (m : ℕ) (b : B) :
    AdicCompletion.evalₐ I (m + 1) (completed I f b) = stage I f m b :=
  AdicPositiveAffineLift.eval_liftHom I _ _ m b

variable [IsAdicComplete I R]

/-- Completeness returns the constructed point to the original base ring. -/
def lift : B →ₐ[R] R :=
  (AdicCompletion.ofAlgEquiv I).symm.toAlgHom.comp (completed I f)

/-- Every original finite-order coordinate is recovered by the complete-base lift. -/
theorem quotient_lift (m : ℕ) (b : B) :
    Ideal.Quotient.mk (I ^ (m + 1)) (lift I f b) = stage I f m b := by
  change Ideal.Quotient.mk _ ((AdicCompletion.ofAlgEquiv I).symm _) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  exact eval_completed I f m b

/-- The actual lifted point restricts to exactly the prescribed quotient point. -/
theorem quotient_comp_lift :
    (Ideal.Quotient.mkₐ R (I ^ 1)).comp (lift I f) = f := by
  ext b
  exact quotient_lift I f 0 b

/-- Formal smoothness and completeness alone supply a lift of every closed quotient point. -/
theorem exists_lift : ∃ g : B →ₐ[R] R, (Ideal.Quotient.mkₐ R (I ^ 1)).comp g = f :=
  ⟨lift I f, quotient_comp_lift I f⟩

variable (f₀ : B →ₐ[R] R ⧸ I)

/-- Lift a point written over the original ideal quotient rather than its first power. -/
def closedLift : B →ₐ[R] R :=
  lift I ((Ideal.quotientEquivAlgOfEq R (pow_one I)).symm.toAlgHom.comp f₀)

/-- The constructed lift has precisely the original closed reduction. -/
theorem quotient_closedLift (b : B) :
    Ideal.Quotient.mk I (closedLift I f₀ b) = f₀ b := by
  have h := quotient_lift I
    ((Ideal.quotientEquivAlgOfEq R (pow_one I)).symm.toAlgHom.comp f₀) 0 b
  have he := congrArg (Ideal.quotientEquivAlgOfEq R (pow_one I)) h
  simpa only [closedLift, stage_zero, Ideal.quotientEquivAlgOfEq_mk, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply] using he

/-- Every original quotient point extends to the same complete base. -/
theorem quotient_comp_closedLift :
    (Ideal.Quotient.mkₐ R I).comp (closedLift I f₀) = f₀ :=
  AlgHom.ext (quotient_closedLift I f₀)

end FLT.Mazur.AdicFormallySmoothLift
