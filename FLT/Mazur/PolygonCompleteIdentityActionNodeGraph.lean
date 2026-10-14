/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionGraphSmooth
public import FLT.Mazur.PolygonCompleteIdentityActionGraphCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Original node-input graph restrictions and the remaining extension test

Every actual node chart has a proper surjective graph restriction carrying a
polygon-valued map. The extension test is invertibility of these constructed
projections. No node-chart inverse or node-input action is assumed as data.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)

/-- The full graph above an actual original node-input neighborhood. -/
abbrev completeIdentityActionNodeGraphOpen (i : Fin n) :
    (completeIdentityActionGraphClosure K n h).Opens :=
  (p) ⁻¹ᵁ completeIdentityActionExtensionOpen K n h (some i)

/-- The original node-chart projection, without altering either original input. -/
abbrev completeIdentityActionNodeGraphProjection (i : Fin n) :=
  (p) ∣_ completeIdentityActionExtensionOpen K n h (some i)

/-- Each actual node-input graph projection is proper. -/
instance completeIdentityActionNodeGraphProjection_proper (i : Fin n) :
    IsProper (completeIdentityActionNodeGraphProjection K n h i) := inferInstance

/-- Every original node-chart input has a point on its constructed graph. -/
instance completeIdentityActionNodeGraphProjection_surjective (i : Fin n) :
    Surjective (completeIdentityActionNodeGraphProjection K n h i) :=
  IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance _

/-- The node graph carries an actual original-polygon-valued morphism. -/
def completeIdentityActionNodeGraphLift (i : Fin n) :
    (completeIdentityActionNodeGraphOpen K n h i).toScheme ⟶ exactVeroneseProj K n h :=
  (completeIdentityActionNodeGraphOpen K n h i).ι ≫ (l)

/-- Its contraction is precisely the original node-input action target. -/
@[reassoc] theorem completeIdentityActionNodeGraphLift_contraction (i : Fin n) :
    completeIdentityActionNodeGraphLift K n h i ≫ (g) =
      completeIdentityActionNodeGraphProjection K n h i ≫
        (completeIdentityActionExtensionOpen K n h (some i)).ι ≫ (a) := by
  rw [completeIdentityActionNodeGraphLift, Category.assoc,
    completeIdentityActionGraphLift_contraction, morphismRestrict_ι_assoc]

/-- Invertibility of the full graph projection is exactly the remaining finite node test. -/
theorem completeIdentityActionGraphProjection_isIso_iff_nodes :
    IsIso (p) ↔ ∀ i : Fin n, IsIso (completeIdentityActionNodeGraphProjection K n h i) := by
  constructor
  · intro hp i
    let _ := hp
    infer_instance
  · intro hn
    apply IsZariskiLocalAtTarget.of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme)
      (completeIdentityActionExtensionOpen K n h)
    · apply top_unique
      intro x _
      obtain ⟨i, hi⟩ := completeActionExtensionOpen_cover K n h
        (completeIdentityActionSecond K n h x)
      exact (le_iSup (completeIdentityActionExtensionOpen K n h) i) hi
    · intro i
      cases i with
      | none => exact completeIdentityActionGraphProjection_smooth_isIso K n h
      | some i => exact hn i

end FLT.Mazur.PolygonInfinitesimalStages
