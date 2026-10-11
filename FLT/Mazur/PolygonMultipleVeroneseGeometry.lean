/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCommonVeroneseStep
public import FLT.Mazur.PolygonMultipleVeroneseStructuralMap
public import FLT.Mazur.PolygonOriginalStageAdicSquare

/-!
# Properness and original adic squares at a multiple step

The proved common-step comparison transfers properness and the actual
cartesian finite-stage squares to every positive multiple of the exact step.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryLine family SectionRetainedProjConstruction.toProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- At the original exact step the new notation is the independently defined original map. -/
theorem originalStageToMultipleProj_exact (m : ℕ) :
    originalStageToMultipleProj K n h (exactVeroneseStep K n h) (dvd_refl _) m =
      originalStageToCompatibleProj K n h m := rfl

variable (r : ℕ) [NeZero r]

/-- Every positive multiple of the exact step remains proper over its original complete base. -/
theorem exactMultipleVeroneseToBase_isProper :
    IsProper (multipleVeroneseToBase K n h (exactVeroneseStep K n h * r)) := by
  rw [← multipleVeroneseProjIso_inv_toBase K n h (exactVeroneseStep K n h) r (NeZero.pos r)]
  let _ : IsProper (multipleVeroneseToBase K n h (exactVeroneseStep K n h)) :=
    exactVeroneseProjToBase_isProper K n h
  infer_instance

/-- At every positive multiple, the actual original stage square is still cartesian. -/
theorem originalStageToExactMultiple_isPullback (m : ℕ) :
    IsPullback
      (originalStageToMultipleProj K n h (exactVeroneseStep K n h * r)
        (dvd_mul_right _ _) m) (family K m n h).hom
      (multipleVeroneseToBase K n h (exactVeroneseStep K n h * r)) (baseToSeries K m) := by
  refine (originalStageToCompatibleProj_isPullback K n h m).of_iso (Iso.refl _)
    (multipleVeroneseProjIso K n h (exactVeroneseStep K n h) r (NeZero.pos r))
    (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_ (by simp)
  · simpa only [Iso.refl_hom, Category.id_comp, originalStageToMultipleProj_exact] using
      originalStageToMultipleProj_comparison K n h (exactVeroneseStep K n h) r (dvd_refl _) m
  · simpa only [Iso.refl_hom, Category.comp_id, multipleVeroneseToBase,
      exactVeroneseProjToBase] using
      (multipleVeroneseProjIso_hom_toBase K n h (exactVeroneseStep K n h) r
        (NeZero.pos r)).symm

end FLT.Mazur.PolygonInfinitesimalStages
