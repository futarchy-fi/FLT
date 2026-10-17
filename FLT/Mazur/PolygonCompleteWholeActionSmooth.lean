/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeAction

/-!
# The full polygon action recovers smooth multiplication

The glued action agrees with the original smooth group multiplication on
all smooth pairs. The formula is also available on arbitrary relative points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "j" => completeWholeSmoothInclusion K n h
local notation "a" => completeWholeAction K n h

/-- The complete action retains the original smooth multiplication on every smooth pair. -/
@[reassoc] theorem completeWholeAction_smooth :
    (𝟙 (M) ⊗ₘ (j)) ≫ (a) = completeSmoothMul K n h ≫ (j) := by
  apply completeSmoothProduct_hom_ext K n h
  intro b c
  have hc := congrArg ((𝟙 (G).X ⊗ₘ completeIdentityChart K n h 0 c) ≫ ·)
    (completeWholeActionChart_smooth K n h b)
  have ht : (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ≫
      (𝟙 (M) ⊗ₘ (j)) =
      (𝟙 (G).X ⊗ₘ completeIdentityChart K n h 0 c) ≫ (𝟙 (G).X ⊗ₘ (j)) ≫
        (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [← Category.assoc, ht, Category.assoc, Category.assoc, completeWholeAction_chart]
  simpa only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id,
    Category.id_comp] using hc

/-- On arbitrary original relative points the full action restricts to the group product. -/
theorem completeWholeAction_smooth_evaluation {T : Over (Spec (.of (PowerSeries K)))}
    (x y : T ⟶ (M)) :
    lift x (y ≫ (j)) ≫ (a) = (lift x y ≫ completeSmoothMul K n h) ≫ (j) := by
  have he := congrArg (lift x y ≫ ·) (completeWholeAction_smooth K n h)
  simpa only [← Category.assoc, lift_map, Category.comp_id] using he

/-- The original whole smooth-by-polygon input is flat over its original base. -/
instance completeWholeActionInput_flat : Flat ((M) ⊗ (X)).hom := by
  let _ : Flat (X).hom := exactVeroneseProjToBase_flat K n h
  exact completeRelative_tensor_flat K (M) (X)

/-- Smooth multiplication uniquely determines an action morphism on the whole input. -/
theorem completeWholeAction_unique (f : (M) ⊗ (X) ⟶ (X))
    (he : (𝟙 (M) ⊗ₘ (j)) ≫ f = completeSmoothMul K n h ≫ (j)) : f = (a) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsSeparated (X).hom := inferInstanceAs
    (IsSeparated (exactVeroneseProjToBase K n h))
  apply completeRelative_smooth_ext K n h (snd (M) (X))
  intro U u y hy
  have hu : u = lift (u ≫ fst _ _) y ≫ (𝟙 (M) ⊗ₘ (j)) := by
    apply hom_ext
    · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
    · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc] using hy
  rw [hu, Category.assoc, Category.assoc, he, completeWholeAction_smooth]

end FLT.Mazur.PolygonInfinitesimalStages
