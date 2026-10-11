/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleCoefficientStageNaturality
public import FLT.Mazur.PolygonMultipleCoefficientStructure
public import FLT.Mazur.PolygonMultipleVeroneseGeometry

/-!
# Coefficient change between the independently chosen complete models

The common product step compares the two original choices without equating them.
The resulting morphism retains every original stage and its power-series base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseStep originalStageToCompatibleProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete coefficient map, transported through the actual common product step. -/
def completeCoefficientProjMap : exactVeroneseProj L n h ⟶ exactVeroneseProj K n h :=
  (commonVeroneseRightIso K L n h).hom ≫
    multipleCoefficientProjMap f n h (commonVeroneseStep K L n h)
      (exactStep_dvd_common_left K L n h) (exactStep_dvd_common_right K L n h) ≫
        (commonVeroneseLeftIso K L n h).inv

/-- The original complete coefficient morphism keeps the actual coefficient map on each stage. -/
@[reassoc]
theorem originalStageToCompatibleProj_coefficient (m : ℕ) :
    originalStageToCompatibleProj L n h m ≫ completeCoefficientProjMap f n h =
      stageCoefficientFamily f m n h ≫ originalStageToCompatibleProj K n h m := by
  have hr : originalStageToCompatibleProj L n h m ≫ (commonVeroneseRightIso K L n h).hom =
      originalStageToMultipleProj L n h _ (exactStep_dvd_common_right K L n h) m :=
    by simpa only [originalStageToMultipleProj_exact] using
      commonVeroneseRightIso_stage K L n h m
  rw [completeCoefficientProjMap, ← Category.assoc, ← Category.assoc, hr,
    originalStageToMultipleProj_coefficient, Category.assoc]
  congr 1
  rw [← commonVeroneseLeftIso_stage, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact originalStageToMultipleProj_exact K n h m

/-- The complete coefficient morphism has the prescribed actual structural square. -/
@[reassoc]
theorem completeCoefficientProjMap_toBase :
    completeCoefficientProjMap f n h ≫ exactVeroneseProjToBase K n h =
      exactVeroneseProjToBase L n h ≫ Spec.map (CommRingCat.ofHom (PowerSeries.map f)) := by
  have hl : (commonVeroneseLeftIso K L n h).inv ≫
      multipleVeroneseToBase K n h (exactVeroneseStep K n h) =
        multipleVeroneseToBase K n h (commonVeroneseStep K L n h) := by
    rw [Iso.inv_comp_eq, commonVeroneseLeftIso_toBase]
  change completeCoefficientProjMap f n h ≫
    multipleVeroneseToBase K n h (exactVeroneseStep K n h) =
      multipleVeroneseToBase L n h (exactVeroneseStep L n h) ≫ _
  simp only [completeCoefficientProjMap, Category.assoc, hl,
    multipleCoefficientProjMap_toBase, commonVeroneseRightIso_toBase_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
