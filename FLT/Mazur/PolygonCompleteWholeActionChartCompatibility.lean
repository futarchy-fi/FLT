/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteRelativeSmoothDetection

/-!
# Compatibility of the whole-polygon action charts

The rotated charts agree on every flat relative test scheme on which their
original parameter and polygon inputs agree. Smooth-input detection retains
the full original schemes throughout the comparison.
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

/-- Smooth evaluation of each whole-input chart is the original smooth product. -/
theorem completeWholeActionChart_evaluation (b : ZMod n)
    {T : Over (Spec (.of (PowerSeries K)))} (x : T ⟶ (G).X) (y : T ⟶ (M)) :
    lift x (y ≫ (j)) ≫ completeWholeActionChart K n h b =
      lift (x ≫ completeIdentityChart K n h 0 b) y ≫ completeSmoothMul K n h ≫ (j) := by
  have he := congrArg (lift x y ≫ ·) (completeWholeActionChart_smooth K n h b)
  simpa only [← Category.assoc, lift_map, Category.comp_id] using he

/-- A pair with smooth second coordinate factors through the actual smooth-input product. -/
theorem completeWholeInput_smooth_factor {T : Over (Spec (.of (PowerSeries K)))}
    (x : T ⟶ (G).X ⊗ (X)) (y : T ⟶ (M)) (he : x ≫ snd _ _ = y ≫ (j)) :
    x = lift (x ≫ fst _ _) y ≫ (𝟙 (G).X ⊗ₘ (j)) := by
  apply hom_ext
  · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
  · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc] using he

/-- Equal original inputs give equal chart actions on any flat relative test scheme. -/
theorem completeWholeActionChart_compatible {T : Over (Spec (.of (PowerSeries K)))}
    [Flat T.hom] (b c : ZMod n) (x y : T ⟶ (G).X ⊗ (X))
    (he : x ≫ (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)) =
      y ≫ (completeIdentityChart K n h 0 c ⊗ₘ 𝟙 (X))) :
    x ≫ completeWholeActionChart K n h b = y ≫ completeWholeActionChart K n h c := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsSeparated (X).hom := inferInstanceAs
    (IsSeparated (exactVeroneseProjToBase K n h))
  have hx := congrArg (· ≫ fst (M) (X)) he
  have hy := congrArg (· ≫ snd (M) (X)) he
  simp only [Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id] at hx hy
  apply completeRelative_smooth_ext K n h (x ≫ snd _ _)
  intro U u z hz
  have hz' : u ≫ y ≫ snd _ _ = z ≫ (j) := by rw [← hy]; exact hz
  have hxf := completeWholeInput_smooth_factor K n h (u ≫ x) z
    (by simpa only [Category.assoc] using hz)
  have hyf := completeWholeInput_smooth_factor K n h (u ≫ y) z
    (by simpa only [Category.assoc] using hz')
  rw [← Category.assoc u x, ← Category.assoc u y, hxf, hyf]
  simp only [Category.assoc, completeWholeActionChart_smooth]
  simp only [← Category.assoc, lift_map, Category.comp_id]
  congr 3
  simpa only [Category.assoc] using congrArg (u ≫ ·) hx

end FLT.Mazur.PolygonInfinitesimalStages
