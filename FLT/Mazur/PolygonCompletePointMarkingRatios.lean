/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicPreimages
public import FLT.Mazur.ModuleSectionRatioAlongMorphism

/-!
# The original complete-base marking evaluated on the Y generator chart

The actual Y-chart lift of the marking evaluates all original section ratios and base scalars.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "e" => completePointSectionFrame K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
open WeierstrassIntegralChart

local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "B" => Scheme.Opens.topIso (X := (exactVeroneseProj K n h)) (U)

/-- The original marking factors through the Y generator open. -/
def completePointMarkingY : S ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (s) (by
    rw [Scheme.Opens.range_ι]
    exact sectionPoleGenerator_contains_marking (s) hI e 3 (T 1)
      (completePointProjectiveY_coefficient K n h i))

/-- This lift is the original marking after the actual open inclusion. -/
@[reassoc] theorem completePointMarkingY_ι :
    completePointMarkingY K n h i ≫ (U).ι = (s) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual normalized ratios on the Y chart evaluate to [0, 1, 0]. -/
theorem completePointMarkingY_ratio (j : Fin 3) :
    (completePointMarkingY K n h i).appTop
      ((B).inv (sectionRatioOn (tensorPower (L) 3) (T 1) (U) le_rfl (T j))) =
        (![0, 1, 0] : Fin 3 → Γ(S, ⊤)) j := by
  erw [openFactor_appTop (s) (U)
    (completePointMarking_preimage_yGenerator K n h i).ge
    _ (completePointMarkingY_ι K n h i)]
  have he := sectionRatioOn_frame (s) (tensorPower (L) 3) (U)
    (completePointMarking_preimage_yGenerator K n h i).ge (T 1) (T j) le_rfl
    (sectionPoleMultiplicativeFrame (s) hI e 3)
    (completePointProjectiveY_coefficient K n h i)
  exact he.trans (completePointProjectiveSections_coefficient K n h i j)

/-- The actual chart scalar map restricts to the identity along the original marking. -/
theorem completePointMarkingY_scalar (a : Γ(S, ⊤)) :
    (completePointMarkingY K n h i).appTop
      ((B).inv (sectionChartScalars (f).appTop.hom (U) a)) = a := by
  erw [openFactor_appTop (s) (U)
    (completePointMarking_preimage_yGenerator K n h i).ge
    _ (completePointMarkingY_ι K n h i)]
  unfold sectionChartScalars
  change (s).appLE (U) ⊤ _ ((exactVeroneseProj K n h).presheaf.map _ ((f).appTop a)) = a
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_eq_app]
  change ((s) ≫ (f)).appTop a = a
  rw [(completeBaseMarking_toBase K n h i)]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
