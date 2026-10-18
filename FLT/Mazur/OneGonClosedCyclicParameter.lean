/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingRelativeGroupSpecialization
public import FLT.Mazur.OneGonSmoothingFaithfulCyclicSubgroup
public import FLT.Mazur.GroupMarkingTransportEquations
public import FLT.Mazur.GroupMarkingBaseProjection
public import FLT.Mazur.AuxiliaryLevelFieldMarking

/-!
# Prescribed closed torus labels in the original cyclic parameter scheme

The actual closed smooth-group comparison sends every faithful torus marking
to a point of the faithful parameter of the complete smoothing. The comparison
recovers each original label. Extending this point over the complete base is a
separate lifting problem.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "G" => relativeGroup (t)
local notation "H" => relativeTestGroup (t) (c)
local notation "L" => Multiplicative (ZMod n)
variable (labels : Multiplicative (ZMod n) →*
  (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))

/-- Original torus labels as sections of the actual closed smooth fiber. -/
def closedCyclicSections : L →* (𝟙_ (Over (Spec (.of K))) ⟶ (H).X) :=
  GroupMarkingTransport.transport _ _ (completeClosedGroupTorusIso K).symm labels

/-- Returning to the torus recovers every prescribed label. -/
theorem closedCyclicSections_compare (a : L) :
    closedCyclicSections K n labels a ≫ (completeClosedGroupTorusIso K).hom.hom.hom.hom =
      labels a :=
  GroupMarkingTransport.transport_compare _ _ (completeClosedGroupTorusIso K).symm labels a

/-- The closed labels projected into the original group over the complete base. -/
def closedCyclicMarking : L →* (Over.mk (c) ⟶ (G).X) where
  toFun a := Over.homMk (𝟙 _) (by simp) ≫
    GroupMarkingBaseChange.projectMarking (c) (G).X (𝟙_ _)
      (closedCyclicSections K n labels) a
  map_one' := by rw [map_one, comp_one]
  map_mul' a b := by rw [map_mul, comp_mul]

/-- Projection retains the entire original closed-fiber label map. -/
theorem closedCyclicMarking_left (a : L) :
    (closedCyclicMarking K n labels a).left =
      (closedCyclicSections K n labels a).left ≫ pullback.fst (G).X.hom (c) := by
  change (𝟙 (Spec (.of K))) ≫ _ = _
  rw [Category.id_comp]
  exact GroupMarkingBaseChange.projectMarking_left (c) (G).X (𝟙_ _)
    (closedCyclicSections K n labels) a

/-- Faithful torus markings remain faithful in the original relative group. -/
theorem closedCyclicMarking_injective (hm : Function.Injective labels) :
    Function.Injective (closedCyclicMarking K n labels) := by
  have hs : Function.Injective (closedCyclicSections K n labels) :=
    (GroupMarkingTransport.transport_injective_iff _ _
      (completeClosedGroupTorusIso K).symm labels).mpr hm
  have hp := (GroupMarkingBaseChange.projectMarking_injective_iff
    (c) (G).X (𝟙_ _) (closedCyclicSections K n labels)).mpr hs
  intro a b hab
  apply hp
  apply Over.OverMorphism.ext
  have he := congrArg Over.Hom.left hab
  change (𝟙 (Spec (.of K))) ≫ _ = (𝟙 (Spec (.of K))) ≫ _ at he
  simpa only [Category.id_comp] using he

variable [NeZero n]

/-- A prescribed faithful closed torus marking gives an actual original parameter point. -/
def closedCyclicParameter (hm : Function.Injective labels) :
    Over.mk (c) ⟶ relativeCyclicParameter (t) n :=
  fieldFaithfulLift (G).X L (c) (closedCyclicMarking K n labels)
    (closedCyclicMarking_injective K n labels hm)

/-- The original parameter point retains all prescribed relative closed labels. -/
@[reassoc] theorem closedCyclicParameter_value (hm : Function.Injective labels) (a : L) :
    closedCyclicParameter K n labels hm ≫ faithfulInclusion (G).X L ≫ value (G).X L a =
      closedCyclicMarking K n labels a :=
  fieldFaithfulLift_value _ _ _ _ _ a

end FLT.Mazur.OneGonSmoothing
