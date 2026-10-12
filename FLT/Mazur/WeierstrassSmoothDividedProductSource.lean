/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothYAffineSource
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The integral product of a smooth parameter chart and a divided chart

The original divided input stays flat. The smooth affine and Y presentations,
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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "H" => WeierstrassDilatation.Coordinate W s b3 b4 b6

/-- The original integral divided chart times the smooth affine/Y source. -/
def SmoothDividedProductRing := H ⊗[R] SmoothYAffineRing W

instance smoothDividedProductCommRing : CommRing (SmoothDividedProductRing W s b3 b4 b6) :=
  inferInstanceAs (CommRing (H ⊗[R] SmoothYAffineRing W))

instance smoothDividedProductAlgebra : Algebra R (SmoothDividedProductRing W s b3 b4 b6) :=
  inferInstanceAs (Algebra R (H ⊗[R] SmoothYAffineRing W))

instance smoothDividedProductAlgebraLeft : Algebra H (SmoothDividedProductRing W s b3 b4 b6) :=
  inferInstanceAs (Algebra H (H ⊗[R] SmoothYAffineRing W))

instance smoothDividedProductTower : IsScalarTower R H (SmoothDividedProductRing W s b3 b4 b6) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (Algebra.TensorProduct.includeLeft (R := R) (A := H)
      (B := SmoothYAffineRing W)).commutes r |>.symm

local notation "S" => SmoothDividedProductRing W s b3 b4 b6
/-- The original smooth parameter projection on the product algebra. -/
def smoothDividedParameter : SmoothYAffineRing W →ₐ[R] S :=
  Algebra.TensorProduct.includeRight

local notation "j" => smoothDividedParameter W s b3 b4 b6

/-- The retained original divided input. -/
def smoothDividedInput : H →+* S := algebraMap H S

/-- The actual original right affine input. -/
def smoothDividedRight : Coordinate W 2 →ₐ[R] S :=
  (Algebra.TensorProduct.includeLeft (R := R) (A := H) (B := SmoothYAffineRing W)).comp
    (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6)

/-- The actual smooth left input in the affine chart. -/
def smoothDividedLeft : Coordinate W 2 →ₐ[R] S := (j).comp (smoothYAffineA W)

/-- The same smooth input in the original Y chart. -/
def smoothDividedY : Coordinate W 1 →ₐ[R] S := (j).comp (smoothYAffineY W)

/-- The genuine smooth point on the integral product. -/
def smoothDividedPoint : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme :=
  Spec.map (CommRingCat.ofHom (j).toRingHom) ≫ smoothYAffinePoint W

/-- The right input contracts to the retained original divided chart. -/
theorem smoothDividedRight_contraction :
    (smoothDividedRight W s b3 b4 b6 h3 h4 h6).toRingHom = (smoothDividedInput W s b3 b4 b6).comp
      (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom := rfl

/-- The divided input is flat before residue restriction. -/
theorem smoothDividedInput_flat : RingHom.Flat (smoothDividedInput W s b3 b4 b6) :=
  RingHom.flat_algebraMap_iff.mpr
    (inferInstanceAs (Module.Flat H (H ⊗[R] SmoothYAffineRing W)))

/-- The left affine presentation is the constructed genuine smooth point. -/
theorem smoothDividedLeft_inclusion :
    Spec.map (CommRingCat.ofHom (smoothDividedLeft W s b3 b4 b6).toRingHom) ≫
      integralCurveChart W 2 = smoothDividedPoint W s b3 b4 b6 ≫ (integralSmoothOpen W).ι := by
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom (j).toRingHom) ≫ f)
    (smoothYAffineA_inclusion W)
  rw [← Category.assoc, ← Spec.map_comp] at h
  exact h

/-- Both normalized presentations still describe the same point after the product pullback. -/
theorem smoothDivided_common :
    Spec.map (CommRingCat.ofHom (smoothDividedLeft W s b3 b4 b6).toRingHom) ≫
      integralCurveChart W 2 =
    Spec.map (CommRingCat.ofHom (smoothDividedY W s b3 b4 b6).toRingHom) ≫
      integralCurveChart W 1 := by
  apply (chart_algHom_global_eq_iff W 2 1 _ _).mpr
  intro i
  change j (smoothYAffineA W (coord W 2 i)) =
    j (smoothYAffineA W (coord W 2 1)) * j (smoothYAffineY W (coord W 1 i))
  rw [(chart_algHom_global_eq_iff W 2 1 _ _).mp (smoothYAffine_common W) i, map_mul]

/-- Both actual inputs lie over the same original coefficient point. -/
theorem smoothDivided_structure :
    smoothDividedPoint W s b3 b4 b6 ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (smoothDividedRight W s b3 b4 b6 h3 h4 h6).toRingHom) ≫
        integralCurveChart W 2) ≫ integralCurveStructure W := by
  rw [integralSmoothStructure, ← Category.assoc, ← smoothDividedLeft_inclusion]
  simp only [Category.assoc, integralCurveChart_structure, chartStructure,
    specAlgHom_structure]

end FLT.Mazur.WeierstrassIntegralChart
