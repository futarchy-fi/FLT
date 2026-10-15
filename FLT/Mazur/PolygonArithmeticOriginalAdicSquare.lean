/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageBaseComparison

/-!
# Actual arithmetic polygon schemes as adic fibers of the compatible Proj

The original section evaluation identifies each original stage, over its
original quotient coefficient ring, with the corresponding adic fiber.
The specified stage markings retain their actual integral-base maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family boundaryLine boundaryStageRetainedIso
  SectionRetainedProjConstruction.toProj exactVeroneseTensorReduction

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original section evaluation into the compatible arithmetic Proj. -/
def originalStageToCompatibleProj (m : ℕ) :
    (family A π m n h).left ⟶ exactVeroneseProj A π n h hne hgen :=
  (boundaryStageRetainedIso A π hne hgen n h m).hom ≫
    boundaryVeroneseProjToCompatible A π n h hne hgen m

/-- Evaluation retains the original integral structure map at every arithmetic order. -/
@[reassoc]
theorem originalStageToCompatibleProj_toBase (m : ℕ) :
    originalStageToCompatibleProj A π hne hgen n h m ≫
        exactVeroneseProjToBase A π n h hne hgen =
      (family A π m n h).hom ≫ baseToIntegral A π m := by
  rw [originalStageToCompatibleProj, Category.assoc,
    boundaryVeroneseProjToCompatible_toBase, boundaryStageRetainedIso_toOriginalBase_assoc]

/-- The original arithmetic stage, with its actual coefficient map, is the actual adic fiber. -/
theorem originalStageToCompatibleProj_isPullback (m : ℕ) :
    IsPullback (originalStageToCompatibleProj A π hne hgen n h m) (family A π m n h).hom
      (exactVeroneseProjToBase A π n h hne hgen) (baseToIntegral A π m) := by
  refine (exactVeroneseProj_adic_isPullback A π n h hne hgen m).of_iso
    (boundaryStageRetainedIso A π hne hgen n h m).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp; rfl)
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      originalStageToCompatibleProj, Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
    rw [← boundaryRetainedProjToOriginalBase_adic,
      boundaryStageRetainedIso_inv_toOriginalBase]

/-- Original arithmetic stages enter the candidate by actual closed immersions. -/
theorem originalStageToCompatibleProj_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (originalStageToCompatibleProj A π hne hgen n h m) := by
  exact MorphismProperty.of_isPullback
    (originalStageToCompatibleProj_isPullback A π hne hgen n h m).flip
    (inferInstanceAs (IsClosedImmersion (baseToIntegral A π m)))

/-- Every original stage marking still has the original integral coefficient morphism. -/
@[reassoc]
theorem originalStageMarking_toBase (m : ℕ) (i : Fin n) :
    marking A π m n h i ≫ originalStageToCompatibleProj A π hne hgen n h m ≫
      exactVeroneseProjToBase A π n h hne hgen = baseToIntegral A π m := by
  rw [originalStageToCompatibleProj_toBase, marking_base_assoc]

end FLT.Mazur.PolygonArithmeticStages
