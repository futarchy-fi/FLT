/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageNaturality

/-!
# Original markings on the actual retained adic stages

Transport the specified polygon markings through the proved recovery.
Their section equations and compatibility retain the original base maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family boundaryLine boundaryStageRetainedIso

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) (n : ℕ) (h : 2 ≤ n)
    [NeZero n]

/-- The original marking transported to the independently constructed retained stage Proj. -/
def retainedStageMarking (m : ℕ) (i : Fin n) :
    Spec (.of (Quotient A π m)) ⟶ boundaryExactVeroneseProj A π n h hne hgen m :=
  marking A π m n h i ≫ (boundaryStageRetainedIso A π hne hgen n h m).hom

/-- Transport retains the original marking's section equation over its original base. -/
@[reassoc]
theorem retainedStageMarking_toOriginalBase (m : ℕ) (i : Fin n) :
    retainedStageMarking A π hne hgen n h m i ≫ boundaryRetainedProjToOriginalBase A π hne hgen n
    h m = 𝟙 _ := by
  rw [retainedStageMarking, Category.assoc, boundaryStageRetainedIso_toOriginalBase,
    marking_base]

/-- Every original marking remains compatible with the independently defined Proj transitions. -/
@[reassoc]
theorem retainedStageMarking_naturality {a b : ℕ} (f : a ⟶ b) (i : Fin n) :
    (baseSystem A π).map f ≫ retainedStageMarking A π hne hgen n h b i =
      retainedStageMarking A π hne hgen n h a i ≫ boundaryVeroneseProjTransition A π hne hgen n h
    f := by
  have hn := (systemMarking A π n h i).naturality f
  change (baseSystem A π).map f ≫ marking A π b n h i =
    marking A π a n h i ≫ (stageSystem A π n h).map f at hn
  rw [retainedStageMarking, retainedStageMarking, Category.assoc,
    boundaryStageRetainedIso_naturality, ← Category.assoc, hn, Category.assoc]

/-- The transported markings remain pairwise disjoint on the original retained stage. -/
theorem retainedStageMarkings_pairwise (m : ℕ) :
    Pairwise (fun i j ↦ Disjoint (Set.range (retainedStageMarking A π hne hgen n h m i))
      (Set.range (retainedStageMarking A π hne hgen n h m j))) := by
  intro i j hij
  change Disjoint
    (Set.range ((boundaryStageRetainedIso A π hne hgen n h m).hom ∘ marking A π m n h i))
    (Set.range ((boundaryStageRetainedIso A π hne hgen n h m).hom ∘ marking A π m n h j))
  rw [Set.range_comp, Set.range_comp]
  exact Set.disjoint_image_of_injective (boundaryStageRetainedIso A π hne hgen n h
    m).hom.homeomorph.injective
    (markings_pairwise A π m n h hij)

/-- The original marked bases form a compatible system of points in the complete candidate. -/
def originalMarkingCompatibleProj (i : Fin n) :
    baseSystem A π ⟶ (Functor.const ℕ).obj (exactVeroneseProj A π n h hne hgen) :=
  systemMarking A π n h i ≫ (originalStageCompatibleProjCocone A π hne hgen n h).ι

/-- Each component of the compatible marked point is the original stage marking and evaluation. -/
theorem originalMarkingCompatibleProj_app (i : Fin n) (m : ℕ) :
    (originalMarkingCompatibleProj A π hne hgen n h i).app m =
      marking A π m n h i ≫ originalStageToCompatibleProj A π hne hgen n h m := rfl

/-- Every finite-order marked point has the original complete-base coefficient map. -/
@[reassoc]
theorem originalMarkingCompatibleProj_toBase (i : Fin n) (m : ℕ) :
    (originalMarkingCompatibleProj A π hne hgen n h i).app m ≫ exactVeroneseProjToBase A π n h hne
    hgen =
      baseToIntegral A π m := by
  rw [originalMarkingCompatibleProj_app, Category.assoc,
    originalStageToCompatibleProj_toBase, marking_base_assoc]

end FLT.Mazur.PolygonArithmeticStages
