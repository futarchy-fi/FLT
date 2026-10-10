/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageRetainedNaturality

/-!
# Original markings on the actual retained adic stages

Transport the specified polygon markings through the proved recovery.
Their section equations and compatibility retain the original base maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family boundaryLine boundaryStageRetainedIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original marking transported to the independently constructed retained stage Proj. -/
def retainedStageMarking (m : ℕ) (i : Fin n) :
    Spec (.of (Ring K m)) ⟶ boundaryExactVeroneseProj K n h m :=
  marking K m n h i ≫ (boundaryStageRetainedIso K n h m).hom

/-- Transport retains the original marking's section equation over its original base. -/
@[reassoc]
theorem retainedStageMarking_toOriginalBase (m : ℕ) (i : Fin n) :
    retainedStageMarking K n h m i ≫ boundaryRetainedProjToOriginalBase K n h m = 𝟙 _ := by
  rw [retainedStageMarking, Category.assoc, boundaryStageRetainedIso_toOriginalBase,
    marking_base]

/-- Every original marking remains compatible with the independently defined Proj transitions. -/
@[reassoc]
theorem retainedStageMarking_naturality {a b : ℕ} (f : a ⟶ b) (i : Fin n) :
    (baseSystem K).map f ≫ retainedStageMarking K n h b i =
      retainedStageMarking K n h a i ≫ boundaryVeroneseProjTransition K n h f := by
  have hn := (systemMarking K n h i).naturality f
  change (baseSystem K).map f ≫ marking K b n h i =
    marking K a n h i ≫ (stageSystem K n h).map f at hn
  rw [retainedStageMarking, retainedStageMarking, Category.assoc,
    boundaryStageRetainedIso_naturality, ← Category.assoc, hn, Category.assoc]

/-- The transported markings remain pairwise disjoint on the original retained stage. -/
theorem retainedStageMarkings_pairwise (m : ℕ) :
    Pairwise (fun i j ↦ Disjoint (Set.range (retainedStageMarking K n h m i))
      (Set.range (retainedStageMarking K n h m j))) := by
  intro i j hij
  change Disjoint
    (Set.range ((boundaryStageRetainedIso K n h m).hom ∘ marking K m n h i))
    (Set.range ((boundaryStageRetainedIso K n h m).hom ∘ marking K m n h j))
  rw [Set.range_comp, Set.range_comp]
  exact Set.disjoint_image_of_injective (boundaryStageRetainedIso K n h m).hom.homeomorph.injective
    (markings_pairwise K m n h hij)

/-- The same actual marking expressed on the specified adic quotient base. -/
def retainedAdicStageMarking (m : ℕ) (i : Fin n) :
    Spec (.of (PowerSeries K ⧸ parameterIdeal K ^ (m + 1))) ⟶
      boundaryExactVeroneseProj K n h m :=
  (stageAdicBaseIso K m).inv ≫ retainedStageMarking K n h m i

/-- The adic marking is a section of W208's actual structural map. -/
@[reassoc]
theorem retainedAdicStageMarking_toBase (m : ℕ) (i : Fin n) :
    retainedAdicStageMarking K n h m i ≫ boundaryVeroneseProjToAdicBase K n h m = 𝟙 _ := by
  rw [retainedAdicStageMarking, ← boundaryRetainedProjToOriginalBase_adic,
    Category.assoc, retainedStageMarking_toOriginalBase_assoc,
    Iso.inv_hom_id]

/-- The original marked bases form a compatible system of points in the complete candidate. -/
def originalMarkingCompatibleProj (i : Fin n) :
    baseSystem K ⟶ (Functor.const ℕ).obj (exactVeroneseProj K n h) :=
  systemMarking K n h i ≫ (originalStageCompatibleProjCocone K n h).ι

/-- Each component of the compatible marked point is the original stage marking and evaluation. -/
theorem originalMarkingCompatibleProj_app (i : Fin n) (m : ℕ) :
    (originalMarkingCompatibleProj K n h i).app m =
      marking K m n h i ≫ originalStageToCompatibleProj K n h m := rfl

/-- Every finite-order marked point has the original complete-base coefficient map. -/
@[reassoc]
theorem originalMarkingCompatibleProj_toBase (i : Fin n) (m : ℕ) :
    (originalMarkingCompatibleProj K n h i).app m ≫ exactVeroneseProjToBase K n h =
      baseToSeries K m := by
  rw [originalMarkingCompatibleProj_app, Category.assoc,
    originalStageToCompatibleProj_toBase, marking_base_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
