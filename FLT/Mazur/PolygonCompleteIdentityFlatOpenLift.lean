/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphFlatExt
public import FLT.Mazur.PolygonCompleteIdentityActionLocalGluing
public import FLT.Mazur.SchemeFlatTargetOpen

/-!
# An actual original action on the full flat target region

The whole graph projection is invertible over its largest flat target open.
Its inverse constructs a polygon-valued lift of the prescribed cubic action.
The open contains the entire smooth input. Its intersections with the original
node charts give actual open lifts; coverage of all node inputs is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "V" => completeIdentityActionSmoothOpen K n h

/-- The largest target open on which the entire original graph projection is flat. -/
def completeIdentityActionFlatOpen : (P).Opens := SchemeFlatTargetOpen.locus (p)
local notation "U" => completeIdentityActionFlatOpen K n h
local notation "q" => SchemeFlatTargetOpen.projection (p)

/-- The full graph over this constructed open is actually isomorphic to the original input. -/
instance completeIdentityActionFlatProjection_isIso : IsIso (q) := by
  let _ : Flat (pullback.snd (p) (U).ι) := SchemeFlatTargetOpen.projection_flat (p)
  exact completeIdentityActionGraphBaseChange_isIso K n h (U).ι

/-- The inverse of the graph projection constructs the original polygon-valued action. -/
def completeIdentityActionFlatLift : (U).toScheme ⟶ exactVeroneseProj K n h :=
  inv (q) ≫ pullback.fst (p) (U).ι ≫ (l)

/-- The constructed open lift contracts to the literal prescribed cubic action. -/
@[reassoc] theorem completeIdentityActionFlatLift_contraction :
    completeIdentityActionFlatLift K n h ≫ (c) = (U).ι ≫ (a) := by
  rw [completeIdentityActionFlatLift, Category.assoc, Category.assoc,
    completeIdentityActionGraphLift_contraction, pullback.condition_assoc]
  exact IsIso.inv_hom_id_assoc (q) _

/-- The constructed lift has the unchanged original power-series base. -/
@[reassoc] theorem completeIdentityActionFlatLift_structure :
    completeIdentityActionFlatLift K n h ≫ exactVeroneseProjToBase K n h =
      (U).ι ≫ completeIdentityActionSecond K n h ≫ exactVeroneseProjToBase K n h :=
  completeIdentityActionLift_structure K n h (U).ι _
    (completeIdentityActionFlatLift_contraction K n h)

/-- The whole original smooth-input open is retained, with no shrinking. -/
theorem completeIdentityActionSmooth_le_flatOpen : (V) ≤ (U) := by
  apply (SchemeFlatTargetOpen.le_locus_iff (p) (V)).mpr
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

/-- The new action agrees exactly with the previously constructed smooth action. -/
@[reassoc] theorem completeIdentityActionFlatLift_smooth :
    (P).homOfLE (completeIdentityActionSmooth_le_flatOpen K n h) ≫
      completeIdentityActionFlatLift K n h = completeIdentityActionSmoothLift K n h := by
  apply completeIdentityActionLift_unique K n h (V).ι
  · rw [Category.assoc, completeIdentityActionFlatLift_contraction,
      ← Category.assoc, Scheme.homOfLE_ι]
  · exact completeIdentityActionSmoothLift_contraction K n h

/-- Each original node chart has a constructed open refinement inside the actual flat region. -/
def completeIdentityActionFlatNodeOpen (i : Fin n) : (P).Opens :=
  (U) ⊓ completeIdentityActionExtensionOpen K n h (some i)

/-- The node refinement carries an actual morphism to the original polygon. -/
def completeIdentityActionFlatNodeLift (i : Fin n) :
    (completeIdentityActionFlatNodeOpen K n h i).toScheme ⟶ exactVeroneseProj K n h :=
  (P).homOfLE (show completeIdentityActionFlatNodeOpen K n h i ≤ (U) from inf_le_left) ≫
    completeIdentityActionFlatLift K n h

/-- These are lifts of the original node-input action, retaining the full open scheme. -/
@[reassoc] theorem completeIdentityActionFlatNodeLift_contraction (i : Fin n) :
    completeIdentityActionFlatNodeLift K n h i ≫ (c) =
      (completeIdentityActionFlatNodeOpen K n h i).ι ≫ (a) := by
  rw [completeIdentityActionFlatNodeLift, Category.assoc,
    completeIdentityActionFlatLift_contraction, ← Category.assoc, Scheme.homOfLE_ι]

/-- No flat original node neighborhood is omitted by the constructed refinement. -/
theorem completeIdentityActionFlatNodeOpen_maximal (i : Fin n) (W : (P).Opens)
    (hW : W ≤ completeIdentityActionExtensionOpen K n h (some i))
    [Flat (pullback.snd (p) W.ι)] : W ≤ completeIdentityActionFlatNodeOpen K n h i :=
  le_inf ((SchemeFlatTargetOpen.le_locus_iff (p) W).mpr inferInstance) hW

end FLT.Mazur.PolygonInfinitesimalStages
