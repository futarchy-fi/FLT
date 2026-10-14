/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityGeneric
public import FLT.Mazur.PolygonCompleteMarkingRotation

/-!
# The original identity open and its cyclic translates

Use the inverse of each actual whole-family rotation to define its translated
open. Restriction gives an isomorphism back to the constructed identity group
carrier, over the unchanged power-series base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "U" => completePointIdentityOpen K n h i
attribute [local instance] exactVeroneseProjToBase_lfp

/-- The original rotation is an automorphism of the unchanged complete family. -/
theorem completeRotation_isIso (a : ZMod n) : IsIso (completeRotation K n h a) := by
  unfold completeRotation
  infer_instance

attribute [local instance] completeRotation_isIso

/-- Translation of the full original identity open by the specified cyclic rotation. -/
def completeRotatedIdentityOpen (a : ZMod n) : (exactVeroneseProj K n h).Opens :=
  completeRotation K n h (-a) ⁻¹ᵁ (U)

/-- The unchanged original rotation preserves the actual smooth open. -/
theorem completeRotation_preimage_smoothLocus (a : ZMod n) :
    completeRotation K n h a ⁻¹ᵁ (f).smoothLocus = (f).smoothLocus := by
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact completeRotation_toBase K n h a

/-- Each translated identity chart remains inside the actual original smooth locus. -/
theorem completeRotatedIdentityOpen_le_smooth (a : ZMod n) :
    completeRotatedIdentityOpen K n h i a ≤ (f).smoothLocus := by
  rw [← completeRotation_preimage_smoothLocus K n h (-a)]
  exact fun _ hx ↦ completePointIdentityOpen_le_smooth K n h i hx

/-- Rotation back to the identity chart is the actual restricted whole-family morphism. -/
def completeRotatedIdentityIso (a : ZMod n) :
    (completeRotatedIdentityOpen K n h i a).toScheme ≅ (U).toScheme := by
  exact asIso (completeRotation K n h (-a) ∣_ (U))

/-- The chart comparison preserves its exact inclusion into the original polygon. -/
@[reassoc] theorem completeRotatedIdentityIso_inclusion (a : ZMod n) :
    (completeRotatedIdentityIso K n h i a).hom ≫ (U).ι =
      (completeRotatedIdentityOpen K n h i a).ι ≫ completeRotation K n h (-a) :=
  morphismRestrict_ι _ _

/-- The inverse chart comparison is the forward original rotation. -/
@[reassoc] theorem completeRotatedIdentityIso_inv_inclusion (a : ZMod n) :
    (completeRotatedIdentityIso K n h i a).inv ≫
      (completeRotatedIdentityOpen K n h i a).ι = (U).ι ≫ completeRotation K n h a := by
  apply (cancel_mono (completeRotation K n h (-a))).mp
  rw [Category.assoc, ← completeRotatedIdentityIso_inclusion, Iso.inv_hom_id_assoc,
    Category.assoc, ← completeRotation_add, add_neg_cancel, completeRotation_zero,
    Category.comp_id]

/-- Each translated chart comparison is over the unchanged original base. -/
@[reassoc] theorem completeRotatedIdentityIso_toBase (a : ZMod n) :
    (completeRotatedIdentityIso K n h i a).hom ≫ (U).ι ≫ (f) =
      (completeRotatedIdentityOpen K n h i a).ι ≫ (f) := by
  rw [completeRotatedIdentityIso_inclusion_assoc, completeRotation_toBase]

/-- The zero translate is exactly the original identity open. -/
@[simp] theorem completeRotatedIdentityOpen_zero :
    completeRotatedIdentityOpen K n h i 0 = (U) := by
  change completeRotation K n h (-0) ⁻¹ᵁ (U) = (U)
  rw [neg_zero, completeRotation_zero]
  rfl

/-- Every translate contains the entire original nonzero-parameter fiber. -/
theorem completeRotatedIdentityOpen_mem_of_parameter_notMem (a : ZMod n)
    (x : exactVeroneseProj K n h) (hx : PowerSeries.X ∉ ((f) x).asIdeal) :
    x ∈ completeRotatedIdentityOpen K n h i a := by
  apply completePointIdentityOpen_mem_of_parameter_notMem K n h i
  have he := congrArg (fun v ↦ v x) (completeRotation_toBase K n h (-a))
  change (f) (completeRotation K n h (-a) x) = (f) x at he
  rwa [he]

end FLT.Mazur.PolygonInfinitesimalStages
