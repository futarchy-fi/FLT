/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityChartAtlas
public import FLT.Mazur.PowerSeriesLaurentGenericOpen

/-!
# Distinct chart presentations force an actual generic field structure

A test scheme represented in two different original translated charts maps
into their proved common open. The Laurent-series comparison then supplies
its field structure and retains its original base morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PowerSeriesLaurentGenericOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "π" => exactVeroneseProjToBase K n h
local notation "V" => completeParameterOpen K n h

/-- The image of a chart belongs to its original rotated open in the whole family. -/
theorem completeIdentityChart_mem (b : ZMod n) (x : (G).X.left) :
    (π).smoothLocus.ι ((completeIdentityChart K n h i b).left x) ∈
      completeRotatedIdentityOpen K n h i b := by
  change (((completeRotatedIdentityIso K n h i b).inv ≫
    completeRotatedIdentityToSmooth K n h i b) ≫ (π).smoothLocus.ι) x ∈ _
  rw [Category.assoc, completeRotatedIdentityToSmooth_inclusion]
  exact ((completeRotatedIdentityIso K n h i b).inv x).property

variable {T : Over (Spec (.of (PowerSeries K)))} (b c : ZMod n) (hbc : b ≠ c)
  (x y : T ⟶ (completePointOriginalBaseGroup K n h i).X)
  (he : x ≫ completeIdentityChart K n h i b = y ≫ completeIdentityChart K n h i c)

include hbc he
/-- An actual pair of distinct chart presentations lands in the common generic open. -/
theorem completeChartOverlap_range :
    Set.range (x.left ≫ (completeIdentityChart K n h i b).left ≫ (π).smoothLocus.ι) ⊆
      Set.range (V).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  rw [← completeRotatedIdentityOpen_inf K n h i b c hbc]
  refine ⟨completeIdentityChart_mem K n h i b (x.left z), ?_⟩
  have he' := congrArg (fun k : T ⟶ completeOriginalSmoothOver K n h ↦
    (π).smoothLocus.ι (k.left z)) he
  change (π).smoothLocus.ι ((completeIdentityChart K n h i b).left (x.left z)) =
    (π).smoothLocus.ι ((completeIdentityChart K n h i c).left (y.left z)) at he'
  change (π).smoothLocus.ι ((completeIdentityChart K n h i b).left (x.left z)) ∈ _
  rw [he']
  exact completeIdentityChart_mem K n h i c (y.left z)

/-- Lift of the unchanged test-scheme map into the actual common generic open. -/
def completeChartOverlapToOpen : T.left ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι
    (x.left ≫ (completeIdentityChart K n h i b).left ≫ (π).smoothLocus.ι)
      (completeChartOverlap_range K n h i b c hbc x y he)

/-- The overlap lift retains the original total-space map. -/
@[reassoc] theorem completeChartOverlapToOpen_inclusion :
    completeChartOverlapToOpen K n h i b c hbc x y he ≫ (V).ι =
      x.left ≫ (completeIdentityChart K n h i b).left ≫ (π).smoothLocus.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- A pair of distinct chart presentations supplies its actual Laurent-series base map. -/
def completeChartOverlapToField : T.left ⟶ Spec (.of (LaurentSeries K)) :=
  completeChartOverlapToOpen K n h i b c hbc x y he ≫ toField K (π)

/-- The induced field structure is over exactly the original power-series base map. -/
@[reassoc] theorem completeChartOverlapToField_base :
    completeChartOverlapToField K n h i b c hbc x y he ≫ genericInclusion K = T.hom := by
  rw [completeChartOverlapToField, Category.assoc, ← (isPullback_toField K (π)).w]
  change completeChartOverlapToOpen K n h i b c hbc x y he ≫ (V).ι ≫ (π) = T.hom
  rw [completeChartOverlapToOpen_inclusion_assoc]
  exact (x ≫ completeIdentityChart K n h i b).w

end FLT.Mazur.PolygonInfinitesimalStages
