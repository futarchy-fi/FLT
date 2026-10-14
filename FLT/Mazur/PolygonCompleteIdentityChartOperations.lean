/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginalBaseGroup
public import FLT.Mazur.PolygonCompleteRotatedIdentityMarking

/-!
# Multiplication and inversion on the translated identity charts

Each chart uses the constructed identity group over the original base.
The local operations land in the chart labeled by the sum or negative.
Compatibility on the generic overlaps is still needed to glue them to
operations on the full original smooth scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "π" => exactVeroneseProjToBase K n h
local notation "U" => completePointIdentityOpen K n h i
local notation "G" => completePointOriginalBaseGroup K n h i
attribute [local instance] exactVeroneseProjToBase_lfp

/-- The full original smooth scheme over its unchanged power-series base. -/
abbrev completeOriginalSmoothOver : Over S₀ := Over.mk ((π).smoothLocus.ι ≫ (π))

/-- Each original rotation embeds a copy of the constructed identity group in the smooth locus. -/
def completeIdentityChart (a : ZMod n) : (G).X ⟶ completeOriginalSmoothOver K n h :=
  Over.homMk ((completeRotatedIdentityIso K n h i a).inv ≫
    completeRotatedIdentityToSmooth K n h i a) (by
      simp only [completeOriginalSmoothOver, Over.mk_hom, Category.assoc,
        completeRotatedIdentityToSmooth_inclusion_assoc,
        completeRotatedIdentityIso_inv_inclusion_assoc, completeRotation_toBase]
      exact (completePointOriginalBaseGroup_structure K n h i).symm)

/-- The chart retains exactly its original complete rotation and original inclusion. -/
@[reassoc] theorem completeIdentityChart_inclusion (a : ZMod n) :
    (completeIdentityChart K n h i a).left ≫ (π).smoothLocus.ι =
      (U).ι ≫ completeRotation K n h a := by
  change ((completeRotatedIdentityIso K n h i a).inv ≫
    completeRotatedIdentityToSmooth K n h i a) ≫ (π).smoothLocus.ι = _
  rw [Category.assoc, completeRotatedIdentityToSmooth_inclusion,
    completeRotatedIdentityIso_inv_inclusion]

/-- Every group-coordinate chart is an open immersion in the original smooth scheme. -/
theorem completeIdentityChart_isOpenImmersion (a : ZMod n) :
    IsOpenImmersion (completeIdentityChart K n h i a).left := by
  change IsOpenImmersion ((completeRotatedIdentityIso K n h i a).inv ≫
    (exactVeroneseProj K n h).homOfLE (completeRotatedIdentityOpen_le_smooth K n h i a))
  infer_instance

/-- The chart's group identity maps to the original cyclically translated marking. -/
@[reassoc] theorem completeIdentityChart_identity (a : ZMod n) :
    (η[(G).X]).left ≫ (completeIdentityChart K n h i a).left ≫ (π).smoothLocus.ι =
      completeBaseMarking K n h (PolygonPinching.rotateIndex a i) := by
  rw [completeIdentityChart_inclusion, completePointOriginalBaseGroup_identity,
    completePointIdentityMarking_inclusion_assoc, completeBaseMarking_rotation]

/-- Actual multiplication in group coordinates, with output in the sum chart. -/
def completeIdentityChartMul (a b : ZMod n) :
    (G).X ⊗ (G).X ⟶ completeOriginalSmoothOver K n h :=
  μ[(G).X] ≫ completeIdentityChart K n h i (a + b)

/-- Actual inversion in group coordinates, with output in the negative chart. -/
def completeIdentityChartInv (a : ZMod n) : (G).X ⟶ completeOriginalSmoothOver K n h :=
  ι[(G).X] ≫ completeIdentityChart K n h i (-a)

/-- Swapping the two input charts preserves their local multiplication morphism. -/
theorem completeIdentityChartMul_comm (a b : ZMod n) :
    (β_ (G).X (G).X).hom ≫ completeIdentityChartMul K n h i b a =
      completeIdentityChartMul K n h i a b := by
  simp only [completeIdentityChartMul, IsCommMonObj.mul_comm_assoc, add_comm]

/-- The zero-chart identity is a left unit for each local multiplication. -/
theorem completeIdentityChartMul_one (a : ZMod n) :
    η[(G).X] ▷ (G).X ≫ completeIdentityChartMul K n h i 0 a =
      (λ_ (G).X).hom ≫ completeIdentityChart K n h i a := by
  rw [completeIdentityChartMul, zero_add, MonObj.one_mul_assoc]

/-- The zero-chart identity is also a right unit for each local multiplication. -/
theorem completeIdentityChartMul_mul_one (a : ZMod n) :
    (G).X ◁ η[(G).X] ≫ completeIdentityChartMul K n h i a 0 =
      (ρ_ (G).X).hom ≫ completeIdentityChart K n h i a := by
  rw [completeIdentityChartMul, add_zero, MonObj.mul_one_assoc]

/-- Inverse coordinates in opposite charts multiply to the original identity chart. -/
theorem completeIdentityChartMul_left_inv (a : ZMod n) :
    CartesianMonoidalCategory.lift ι[(G).X] (𝟙 (G).X) ≫
        completeIdentityChartMul K n h i (-a) a =
      CartesianMonoidalCategory.toUnit (G).X ≫ η[(G).X] ≫
        completeIdentityChart K n h i 0 := by
  rw [completeIdentityChartMul, neg_add_cancel, GrpObj.left_inv_assoc]

/-- The local multiplication retains the original sum rotation after inclusion. -/
@[reassoc] theorem completeIdentityChartMul_inclusion (a b : ZMod n) :
    (completeIdentityChartMul K n h i a b).left ≫ (π).smoothLocus.ι =
      (μ[(G).X]).left ≫ (U).ι ≫ completeRotation K n h (a + b) := by
  change ((μ[(G).X]).left ≫ (completeIdentityChart K n h i (a + b)).left) ≫ _ = _
  rw [Category.assoc, completeIdentityChart_inclusion]

/-- Local inversion retains the original negative rotation after inclusion. -/
@[reassoc] theorem completeIdentityChartInv_inclusion (a : ZMod n) :
    (completeIdentityChartInv K n h i a).left ≫ (π).smoothLocus.ι =
      (ι[(G).X]).left ≫ (U).ι ≫ completeRotation K n h (-a) := by
  change ((ι[(G).X]).left ≫ (completeIdentityChart K n h i (-a)).left) ≫ _ = _
  rw [Category.assoc, completeIdentityChart_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
