/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageRetainedBaseComparison

/-!
# The original polygon schemes are adic fibers of the compatible Proj

The actual section-evaluation recovery and coefficient comparison transport
the Cartesian square to the original schemes and original structure maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family boundaryLine boundaryStageRetainedIso
  SectionRetainedProjConstruction.toProj exactVeroneseTensorReduction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original section evaluation into the complete-base compatible Proj. -/
def originalStageToCompatibleProj (m : ℕ) :
    (family K m n h).left ⟶ exactVeroneseProj K n h :=
  (boundaryStageRetainedIso K n h m).hom ≫ boundaryVeroneseProjToCompatible K n h m

/-- The actual stage evaluation keeps the original power-series structure map. -/
@[reassoc]
theorem originalStageToCompatibleProj_toBase (m : ℕ) :
    originalStageToCompatibleProj K n h m ≫ exactVeroneseProjToBase K n h =
      (family K m n h).hom ≫ baseToSeries K m := by
  rw [originalStageToCompatibleProj, Category.assoc,
    boundaryVeroneseProjToCompatible_toBase, boundaryStageRetainedIso_toOriginalBase_assoc]

/-- The recovery isomorphism is also over the actual adic quotient base. -/
@[reassoc]
theorem boundaryStageRetainedIso_toAdicBase (m : ℕ) :
    (boundaryStageRetainedIso K n h m).hom ≫ boundaryVeroneseProjToAdicBase K n h m =
      (family K m n h).hom ≫ (stageAdicBaseIso K m).hom := by
  rw [← boundaryRetainedProjToOriginalBase_adic,
    boundaryStageRetainedIso_toOriginalBase_assoc]

/-- The original stage scheme with its original base morphism is the actual adic fiber. -/
theorem originalStageToCompatibleProj_isPullback (m : ℕ) :
    IsPullback (originalStageToCompatibleProj K n h m) (family K m n h).hom
      (exactVeroneseProjToBase K n h) (baseToSeries K m) := by
  refine (exactVeroneseProj_adic_isPullback K n h m).of_iso
    (boundaryStageRetainedIso K n h m).symm (Iso.refl _)
    (stageAdicBaseIso K m).symm (Iso.refl _) ?_ ?_ (by simp) ?_
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      originalStageToCompatibleProj, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom]
    rw [← boundaryRetainedProjToOriginalBase_adic, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, boundaryStageRetainedIso_inv_toOriginalBase]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
    rw [← stageAdicBaseIso_toSeries K m, Iso.inv_hom_id_assoc]

/-- The actual adic structural map is flat, inherited from the original stage. -/
theorem boundaryVeroneseProjToAdicBase_flat (m : ℕ) :
    Flat (boundaryVeroneseProjToAdicBase K n h m) := by
  rw [← boundaryRetainedProjToOriginalBase_adic]
  let _ := boundaryRetainedProjToOriginalBase_flat K n h m
  infer_instance

/-- The actual adic structural map is proper, inherited from the original stage. -/
theorem boundaryVeroneseProjToAdicBase_proper (m : ℕ) :
    IsProper (boundaryVeroneseProjToAdicBase K n h m) := by
  rw [← boundaryRetainedProjToOriginalBase_adic]
  let _ := boundaryRetainedProjToOriginalBase_proper K n h m
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
