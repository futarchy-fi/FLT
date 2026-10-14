/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityChartOperations

/-!
# The original smooth polygon has an atlas by copies of its identity group

All chart domains are the constructed original identity open. On the common
generic open their coordinate changes are exactly the original cyclic
rotations. This isolates the translation comparison needed for group gluing.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "U" => completePointIdentityOpen K n h i
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "V" => completeParameterOpen K n h
attribute [local instance] exactVeroneseProjToBase_lfp

/-- Copies of the constructed identity group cover the entire original smooth scheme. -/
def completeIdentityChartCover : (π).smoothLocus.toScheme.OpenCover where
  I₀ := ZMod n
  X _ := (G).X.left
  f a := (completeIdentityChart K n h i a).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, completeIdentityChart_isOpenImmersion K n h i⟩
    have hx : x.1 ∈ ⨆ a : ZMod n, completeRotatedIdentityOpen K n h i a := by
      rw [completeRotatedIdentityOpen_iSup]
      exact x.2
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    let y : (completeRotatedIdentityOpen K n h i a).toScheme := ⟨x.1, ha⟩
    refine ⟨a, (completeRotatedIdentityIso K n h i a).hom y, ?_⟩
    apply (π).smoothLocus.ι.isOpenEmbedding.injective
    change ((completeRotatedIdentityIso K n h i a).hom ≫
      (completeIdentityChart K n h i a).left ≫ (π).smoothLocus.ι) y = _
    change ((completeRotatedIdentityIso K n h i a).hom ≫
      ((completeRotatedIdentityIso K n h i a).inv ≫
        completeRotatedIdentityToSmooth K n h i a) ≫ (π).smoothLocus.ι) y = _
    rw [← Category.assoc, Iso.hom_inv_id_assoc, completeRotatedIdentityToSmooth_inclusion]
    rfl

/-- The original generic open lies in every translated chart. -/
theorem completeParameterOpen_le_rotatedIdentity (a : ZMod n) :
    (V) ≤ completeRotatedIdentityOpen K n h i a :=
  fun x hx ↦ completeRotatedIdentityOpen_mem_of_parameter_notMem K n h i a x hx

/-- Coordinates of the actual generic open in the chart with the specified cyclic label. -/
def completeIdentityGenericCoordinate (a : ZMod n) : (V).toScheme ⟶ (U).toScheme :=
  (exactVeroneseProj K n h).homOfLE (completeParameterOpen_le_rotatedIdentity K n h i a) ≫
    (completeRotatedIdentityIso K n h i a).hom

/-- Generic chart coordinates are exactly restriction of the original negative rotation. -/
@[reassoc] theorem completeIdentityGenericCoordinate_inclusion (a : ZMod n) :
    completeIdentityGenericCoordinate K n h i a ≫ (U).ι =
      (V).ι ≫ completeRotation K n h (-a) := by
  rw [completeIdentityGenericCoordinate, Category.assoc, completeRotatedIdentityIso_inclusion,
    Scheme.homOfLE_ι_assoc]

/-- All generic coordinate maps give the unchanged point in the original smooth scheme. -/
@[reassoc] theorem completeIdentityGenericCoordinate_chart (a : ZMod n) :
    completeIdentityGenericCoordinate K n h i a ≫ (completeIdentityChart K n h i a).left ≫
      (π).smoothLocus.ι = (V).ι := by
  rw [completeIdentityChart_inclusion, completeIdentityGenericCoordinate_inclusion_assoc,
    ← completeRotation_add, neg_add_cancel, completeRotation_zero, Category.comp_id]

/-- Changing generic chart coordinates is exactly the original difference rotation. -/
theorem completeIdentityGenericCoordinate_transition (a b : ZMod n) :
    completeIdentityGenericCoordinate K n h i a ≫ (U).ι ≫ completeRotation K n h (a - b) =
      completeIdentityGenericCoordinate K n h i b ≫ (U).ι := by
  rw [completeIdentityGenericCoordinate_inclusion_assoc,
    completeIdentityGenericCoordinate_inclusion, ← completeRotation_add]
  congr 2
  abel

end FLT.Mazur.PolygonInfinitesimalStages
