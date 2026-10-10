/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorTransition
public import FLT.Mazur.WeierstrassSuccessiveXSchemeOverlap
public import FLT.Mazur.WeierstrassSuccessiveXBaseChangeCoordinates
public import FLT.Mazur.WeierstrassDilatationResidueRetained

/-!
# Base change of the original integral successive overlap

The overlap between the localized tensor algebras is obtained by tensoring
the original integral overlap equivalence. The retained comparison square
holds on every original localized function.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]
local notation "x" => WeierstrassDilatation.x W (s * π) b3 b4 b6
local notation "t" => coord W s π b3 b4 b6 0

/-- The tensor incidence principal open, before any residue normalization. -/
abbrev TensorXOpen := Localization.Away (tensorCoord W s π b3 b4 b6 S 0)

/-- The tensor divided principal open, with the integral scale s*π retained. -/
abbrev TensorDividedOpen := Localization.Away
  (WeierstrassDilatation.tensorX W (s * π) b3 b4 b6 S)

/-- The original integral incidence open included in its actual tensor principal open. -/
def tensorXOpenCoefficient : XOpen W s π b3 b4 b6 →ₐ[R] TensorXOpen W s π b3 b4 b6 S :=
  PrincipalOpenTensor.coefficient (R := R) S t

/-- The original integral divided open included in its actual tensor principal open. -/
def tensorDividedOpenCoefficient : DividedOpen W s π b3 b4 b6 →ₐ[R]
    TensorDividedOpen W s π b3 b4 b6 S :=
  PrincipalOpenTensor.coefficient (R := R) S x

/-- The actual tensor base change of the original integral overlap equivalence. -/
def tensorOverlapEquiv : TensorDividedOpen W s π b3 b4 b6 S ≃ₐ[S]
    TensorXOpen W s π b3 b4 b6 S :=
  PrincipalOpenTensor.transition S x t (overlapEquiv W s π b3 b4 b6)

/-- This transition retains the original integral overlap on every localized function. -/
theorem tensorOverlapEquiv_coefficient (z : DividedOpen W s π b3 b4 b6) :
    tensorOverlapEquiv W s π b3 b4 b6 S (tensorDividedOpenCoefficient W s π b3 b4 b6 S z) =
      tensorXOpenCoefficient W s π b3 b4 b6 S (overlapEquiv W s π b3 b4 b6 z) :=
  PrincipalOpenTensor.transition_coefficient S x t (overlapEquiv W s π b3 b4 b6) z

/-- Coefficient extension of the incidence open retains every original chart function. -/
@[simp] theorem tensorXOpenCoefficient_base (z : Coordinate W s π b3 b4 b6) :
    tensorXOpenCoefficient W s π b3 b4 b6 S (algebraMap _ _ z) =
      algebraMap (ScalarExtension W s π b3 b4 b6 S) _ ((1 : S) ⊗ₜ[R] z) :=
  PrincipalOpenTensor.coefficient_base S t z

/-- Coefficient extension of the divided open retains every original divided function. -/
@[simp] theorem tensorDividedOpenCoefficient_base
    (z : WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6) :
    tensorDividedOpenCoefficient W s π b3 b4 b6 S (algebraMap _ _ z) =
      algebraMap (WeierstrassDilatation.ScalarExtension W (s * π) b3 b4 b6 S) _
        ((1 : S) ⊗ₜ[R] z) :=
  PrincipalOpenTensor.coefficient_base S x z

end FLT.Mazur.WeierstrassSuccessiveX
