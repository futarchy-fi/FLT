/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionGraph
public import FLT.Mazur.PolygonCompleteIdentityActionRotatedMultiplication

/-!
# Original smooth input pairs in the complete cubic graph

The full smooth action product maps into the actual graph closure. On every
rotated identity chart its target is the original multiplication and rotation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "f" => completeIdentitySmoothActionInput K n h

/-- The entire original smooth pair factors through the actual smooth-input open. -/
def completeIdentitySmoothInputToOpen : ((G).X ⊗ (M)).left ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι (f) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change ((f) ≫ completeIdentityActionSecond K n h) x ∈ (π).smoothLocus
    rw [completeIdentitySmoothActionInput_snd]
    exact ((pullback.snd (G).X.hom (M).hom) x).2)

/-- The factorization preserves the original full pair input. -/
@[reassoc] theorem completeIdentitySmoothInputToOpen_input :
    completeIdentitySmoothInputToOpen K n h ≫ (V).ι = (f) :=
  IsOpenImmersion.lift_fac _ _ _

/-- Extracting coordinates recovers the entire smooth pair, including its coefficient maps. -/
@[reassoc] theorem completeIdentitySmoothInputToOpen_coordinates :
    completeIdentitySmoothInputToOpen K n h ≫
      completeIdentityActionSmoothCoordinates K n h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityActionSmoothCoordinates, pullback.lift_fst,
      completeIdentitySmoothInputToOpen_input_assoc, completeIdentitySmoothActionInput_fst,
      Category.id_comp]
  · apply (cancel_mono (π).smoothLocus.ι).mp
    rw [Category.assoc, Category.assoc, completeIdentityActionSmoothCoordinates,
      pullback.lift_snd_assoc, morphismRestrict_ι,
      completeIdentitySmoothInputToOpen_input_assoc, completeIdentitySmoothActionInput_snd,
      Category.id_comp]

/-- The smooth-open lift is the unchanged full smooth multiplication. -/
@[reassoc] theorem completeIdentitySmoothInputToOpen_lift :
    completeIdentitySmoothInputToOpen K n h ≫ completeIdentityActionSmoothLift K n h =
      (completeIdentitySmoothAction K n h).left ≫ (π).smoothLocus.ι := by
  rw [completeIdentityActionSmoothLift,
    completeIdentitySmoothInputToOpen_coordinates_assoc]

/-- Every original smooth pair lies in the actual complete graph closure. -/
def completeIdentitySmoothInputToGraph :
    ((G).X ⊗ (M)).left ⟶ completeIdentityActionGraphClosure K n h :=
  completeIdentitySmoothInputToOpen K n h ≫ completeIdentityActionSmoothToGraph K n h

/-- The graph projection is exactly the full smooth pair's original input. -/
@[reassoc] theorem completeIdentitySmoothInputToGraph_source :
    completeIdentitySmoothInputToGraph K n h ≫ completeIdentityActionGraphProjection K n h =
      (f) := by
  rw [completeIdentitySmoothInputToGraph, Category.assoc,
    completeIdentityActionSmoothToGraph_projection, completeIdentitySmoothInputToOpen_input]

/-- The graph target is the full original smooth action. -/
@[reassoc] theorem completeIdentitySmoothInputToGraph_target :
    completeIdentitySmoothInputToGraph K n h ≫ completeIdentityActionGraphLift K n h =
      (completeIdentitySmoothAction K n h).left ≫ (π).smoothLocus.ι := by
  rw [completeIdentitySmoothInputToGraph, Category.assoc,
    completeIdentityActionSmoothToGraph_lift, completeIdentitySmoothInputToOpen_lift]

/-- Each rotated pair has the actual original multiplication as its graph target. -/
@[reassoc] theorem completeIdentitySmoothInputToGraph_rotated (b : ZMod n) :
    (𝟙 (G).X ⊗ₘ completeIdentityChart K n h 0 b).left ≫
        completeIdentitySmoothInputToGraph K n h ≫ completeIdentityActionGraphLift K n h =
      (μ[(G).X]).left ≫ (completePointIdentityOpen K n h 0).ι ≫
        completeRotation K n h b := by
  rw [completeIdentitySmoothInputToGraph_target, ← Category.assoc]
  have he := congrArg Over.Hom.left (completeIdentitySmoothAction_chart K n h b)
  change _ ≫ (completeIdentitySmoothAction K n h).left =
    (μ[(G).X]).left ≫ (completeIdentityChart K n h 0 b).left at he
  rw [he, Category.assoc, completeIdentityChart_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
