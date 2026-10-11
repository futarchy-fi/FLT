/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothYAffineSource
public import FLT.Mazur.WeierstrassSecantHorizontalResidueFactor

/-!
# The integral product of a smooth parameter chart and a horizontal fraction chart

The original fraction input stays flat. The smooth affine and Y presentations,
their common curve point, and coefficient compatibility are constructed on
this single source before taking any residue or ordinary secant refinement.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)
/-- A named type for the original fraction algebra keeps tensor operations sealed. -/
def HorizontalSourceRing : Type u :=
  BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0)

instance horizontalSourceCommRing : CommRing (HorizontalSourceRing W s) :=
  inferInstanceAs (CommRing
    (BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0)))

instance horizontalSourceAlgebra : Algebra R (HorizontalSourceRing W s) :=
  inferInstanceAs (Algebra R
    (BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0)))

instance horizontalSourceAlgebraChart : Algebra (Coordinate W 2) (HorizontalSourceRing W s) :=
  inferInstanceAs (Algebra (Coordinate W 2)
    (BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0)))

instance horizontalSourceTower : IsScalarTower R (Coordinate W 2) (HorizontalSourceRing W s) :=
  inferInstanceAs (IsScalarTower R (Coordinate W 2)
    (BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0)))

local notation "H" => HorizontalSourceRing W s

/-- The original integral horizontal chart times the smooth affine/Y source. -/
def SmoothHorizontalProductRing := H ⊗[R] SmoothYAffineRing W

instance smoothHorizontalProductCommRing : CommRing (SmoothHorizontalProductRing W s) :=
  inferInstanceAs (CommRing (H ⊗[R] SmoothYAffineRing W))

instance smoothHorizontalProductAlgebra : Algebra R (SmoothHorizontalProductRing W s) :=
  inferInstanceAs (Algebra R (H ⊗[R] SmoothYAffineRing W))

instance smoothHorizontalProductAlgebraLeft : Algebra H (SmoothHorizontalProductRing W s) :=
  inferInstanceAs (Algebra H (H ⊗[R] SmoothYAffineRing W))

instance smoothHorizontalProductTower : IsScalarTower R H (SmoothHorizontalProductRing W s) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (Algebra.TensorProduct.includeLeft (R := R) (A := H)
      (B := SmoothYAffineRing W)).commutes r |>.symm

local notation "S" => SmoothHorizontalProductRing W s
/-- The original smooth parameter projection on the product algebra. -/
def smoothHorizontalParameter : SmoothYAffineRing W →ₐ[R] S :=
  Algebra.TensorProduct.includeRight

local notation "j" => smoothHorizontalParameter W s

/-- The retained original horizontal fraction input. -/
def smoothHorizontalInput : H →+* S := algebraMap H S

/-- The actual original right affine input. -/
def smoothHorizontalRight : Coordinate W 2 →ₐ[R] S :=
  (Algebra.TensorProduct.includeLeft (R := R) (A := H) (B := SmoothYAffineRing W)).comp
    (IsScalarTower.toAlgHom R (Coordinate W 2) H)

/-- The actual smooth left input in the affine chart. -/
def smoothHorizontalLeft : Coordinate W 2 →ₐ[R] S := (j).comp (smoothYAffineA W)

/-- The same smooth input in the original Y chart. -/
def smoothHorizontalY : Coordinate W 1 →ₐ[R] S := (j).comp (smoothYAffineY W)

/-- The genuine smooth point on the integral product. -/
def smoothHorizontalPoint : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme :=
  Spec.map (CommRingCat.ofHom (j).toRingHom) ≫ smoothYAffinePoint W

/-- The right input contracts to the retained original fraction chart. -/
theorem smoothHorizontalRight_contraction :
    (smoothHorizontalRight W s).toRingHom = (smoothHorizontalInput W s).comp
      (algebraMap (Coordinate W 2) H) := rfl

/-- The fraction input is flat before residue restriction. -/
theorem smoothHorizontalInput_flat : RingHom.Flat (smoothHorizontalInput W s) :=
  RingHom.flat_algebraMap_iff.mpr
    (inferInstanceAs (Module.Flat H (H ⊗[R] SmoothYAffineRing W)))

/-- The left affine presentation is the constructed genuine smooth point. -/
theorem smoothHorizontalLeft_inclusion :
    Spec.map (CommRingCat.ofHom (smoothHorizontalLeft W s).toRingHom) ≫
      integralCurveChart W 2 = smoothHorizontalPoint W s ≫ (integralSmoothOpen W).ι := by
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom (j).toRingHom) ≫ f)
    (smoothYAffineA_inclusion W)
  rw [← Category.assoc, ← Spec.map_comp] at h
  exact h

/-- Both normalized presentations still describe the same point after the product pullback. -/
theorem smoothHorizontal_common :
    Spec.map (CommRingCat.ofHom (smoothHorizontalLeft W s).toRingHom) ≫
      integralCurveChart W 2 =
    Spec.map (CommRingCat.ofHom (smoothHorizontalY W s).toRingHom) ≫
      integralCurveChart W 1 := by
  apply (chart_algHom_global_eq_iff W 2 1 _ _).mpr
  intro i
  change j (smoothYAffineA W (coord W 2 i)) =
    j (smoothYAffineA W (coord W 2 1)) * j (smoothYAffineY W (coord W 1 i))
  rw [(chart_algHom_global_eq_iff W 2 1 _ _).mp (smoothYAffine_common W) i, map_mul]

/-- Both actual inputs lie over the same original coefficient point. -/
theorem smoothHorizontal_structure :
    smoothHorizontalPoint W s ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (smoothHorizontalRight W s).toRingHom) ≫
        integralCurveChart W 2) ≫ integralCurveStructure W := by
  rw [integralSmoothStructure, ← Category.assoc, ← smoothHorizontalLeft_inclusion]
  simp only [Category.assoc, integralCurveChart_structure, chartStructure,
    specAlgHom_structure]

end FLT.Mazur.WeierstrassIntegralChart
