/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeActionEvaluation

/-!
# Universal shear on the original smooth-by-whole family

The full action gives an automorphism `(g, x) ↦ (g, g*x)` over the original
smooth parameter scheme. Its inverse uses the constructed smooth inversion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "a" => completeWholeAction K n h

/-- Inverse parameters cancel on arbitrary original test points. -/
theorem completeWholeAction_inverse_evaluation {T : Over (Spec (.of (PowerSeries K)))}
    (g : T ⟶ (M)) (x : T ⟶ (X)) :
    lift g⁻¹ (lift g x ≫ (a)) ≫ (a) = x := by
  rw [← completeWholeAction_associative_evaluation, inv_mul_cancel,
    completeWholeAction_unit_evaluation]

/-- Parameters cancel their inverses on arbitrary original test points. -/
theorem completeWholeAction_inverse_evaluation' {T : Over (Spec (.of (PowerSeries K)))}
    (g : T ⟶ (M)) (x : T ⟶ (X)) :
    lift g (lift g⁻¹ x ≫ (a)) ≫ (a) = x := by
  rw [← completeWholeAction_associative_evaluation, mul_inv_cancel,
    completeWholeAction_unit_evaluation]

/-- The universal original shear retains its actual smooth parameter. -/
def completeWholeShearHom : (M) ⊗ (X) ⟶ (M) ⊗ (X) := lift (fst _ _) (a)

/-- The inverse shear acts by the inverse of the same original parameter. -/
def completeWholeShearInv : (M) ⊗ (X) ⟶ (M) ⊗ (X) :=
  lift (fst _ _) (lift (fst _ _ ≫ completeSmoothInv K n h) (snd _ _) ≫ (a))

/-- Evaluation of the original shear on all relative tests. -/
@[reassoc] theorem completeWholeShearHom_evaluation
    {T : Over (Spec (.of (PowerSeries K)))} (g : T ⟶ (M)) (x : T ⟶ (X)) :
    lift g x ≫ completeWholeShearHom K n h = lift g (lift g x ≫ (a)) := by
  simp only [completeWholeShearHom, comp_lift, lift_fst]

/-- Evaluation of the inverse shear on all relative tests. -/
@[reassoc] theorem completeWholeShearInv_evaluation
    {T : Over (Spec (.of (PowerSeries K)))} (g : T ⟶ (M)) (x : T ⟶ (X)) :
    lift g x ≫ completeWholeShearInv K n h = lift g (lift g⁻¹ x ≫ (a)) := by
  change _ = lift g (lift (g ≫ completeSmoothInv K n h) x ≫ (a))
  simp only [completeWholeShearInv, comp_lift, lift_fst, lift_snd,
    comp_lift_assoc, lift_fst_assoc]

/-- The universal shear is an actual automorphism of the whole original product. -/
def completeWholeShearIso : (M) ⊗ (X) ≅ (M) ⊗ (X) where
  hom := completeWholeShearHom K n h
  inv := completeWholeShearInv K n h
  hom_inv_id := by
    rw [completeWholeShearHom, completeWholeShearInv_evaluation]
    have he := completeWholeAction_inverse_evaluation K n h (fst (M) (X)) (snd (M) (X))
    simpa only [lift_fst_snd, Category.id_comp] using congrArg (lift (fst (M) (X))) he
  inv_hom_id := by
    rw [completeWholeShearInv, completeWholeShearHom_evaluation]
    have he := completeWholeAction_inverse_evaluation' K n h (fst (M) (X)) (snd (M) (X))
    change lift (fst (M) (X))
      (lift (fst (M) (X) ≫ completeSmoothInv K n h) (snd (M) (X)) ≫ (a)) ≫
      (a) = snd (M) (X) at he
    simpa only [lift_fst_snd] using congrArg (lift (fst (M) (X))) he

/-- The universal shear lies over the identity of the original smooth parameter scheme. -/
@[reassoc] theorem completeWholeShearHom_fst :
    completeWholeShearHom K n h ≫ fst (M) (X) = fst _ _ := lift_fst _ _

/-- The second projection of the shear is exactly the original full action. -/
@[reassoc] theorem completeWholeShearHom_snd :
    completeWholeShearHom K n h ≫ snd (M) (X) = (a) := lift_snd _ _

end FLT.Mazur.PolygonInfinitesimalStages
