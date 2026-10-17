/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeActionSmooth

/-!
# Unit and associativity of the entire original polygon action

Flat smooth-input detection extends the existing group laws across every
singular input. The resulting laws are equalities of original morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "j" => completeWholeSmoothInclusion K n h
local notation "a" => completeWholeAction K n h

/-- Associativity holds on every flat original relative test scheme. -/
theorem completeWholeAction_flat_associative {T : Over (Spec (.of (PowerSeries K)))}
    [Flat T.hom] (x y : T ⟶ (M)) (z : T ⟶ (X)) :
    lift (lift x y ≫ completeSmoothMul K n h) z ≫ (a) =
      lift x (lift y z ≫ (a)) ≫ (a) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsSeparated (X).hom := inferInstanceAs
    (IsSeparated (exactVeroneseProjToBase K n h))
  apply completeRelative_smooth_ext K n h z
  intro U u v hv
  simp only [comp_lift_assoc]
  rw [hv]
  simp only [completeWholeAction_smooth_evaluation]
  change (((u ≫ x) * (u ≫ y)) * v) ≫ (j) =
    ((u ≫ x) * ((u ≫ y) * v)) ≫ (j)
  rw [_root_.mul_assoc]

/-- The original smooth identity acts as the identity on the entire original polygon. -/
theorem completeWholeAction_unit :
    lift (toUnit (X) ≫ completeSmoothOne K n h) (𝟙 (X)) ≫ (a) = 𝟙 (X) := by
  let _ : Flat (X).hom := exactVeroneseProjToBase_flat K n h
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsSeparated (X).hom := inferInstanceAs
    (IsSeparated (exactVeroneseProjToBase K n h))
  apply completeRelative_smooth_ext K n h (𝟙 (X))
  intro U u v hv
  simp only [Category.comp_id] at hv ⊢
  rw [comp_lift_assoc, Category.comp_id]
  simp only [← Category.assoc, comp_toUnit]
  rw [hv, completeWholeAction_smooth_evaluation]
  change ((1 : U ⟶ (M)) * v) ≫ (j) = v ≫ (j)
  rw [_root_.one_mul]

/-- The complete action is associative as an equality on the full original triple product. -/
theorem completeWholeAction_assoc :
    (completeSmoothMul K n h ▷ (X)) ≫ (a) =
      (α_ (M) (M) (X)).hom ≫ ((M) ◁ (a)) ≫ (a) := by
  let _ : Flat ((M) ⊗ (M)).hom := completeRelative_tensor_flat K (M) (M)
  let _ : Flat (X).hom := exactVeroneseProjToBase_flat K n h
  let _ : Flat (((M) ⊗ (M)) ⊗ (X)).hom :=
    completeRelative_tensor_flat K ((M) ⊗ (M)) (X)
  have he := completeWholeAction_flat_associative K n h
    (fst ((M) ⊗ (M)) (X) ≫ fst _ _) (fst ((M) ⊗ (M)) (X) ≫ snd _ _) (snd _ _)
  have hi : 𝟙 (((M) ⊗ (M)) ⊗ (X)) =
      lift (lift (fst ((M) ⊗ (M)) (X) ≫ fst _ _)
        (fst ((M) ⊗ (M)) (X) ≫ snd _ _)) (snd _ _) := by
    simp only [← comp_lift, lift_fst_snd, Category.comp_id]
  rw [← Category.id_comp (completeSmoothMul K n h ▷ (X)), hi,
    Category.assoc, lift_whiskerRight_assoc]
  conv_rhs => rw [← Category.id_comp (α_ (M) (M) (X)).hom, hi]
  simpa only [Category.assoc, lift_lift_associator_hom_assoc,
    lift_whiskerLeft_assoc] using he

end FLT.Mazur.PolygonInfinitesimalStages
