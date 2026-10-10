/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTensorOverlap
public import FLT.Mazur.WeierstrassSuccessiveXResidueDividedOverlap

/-!
# The integral depth overlap and its actual residue base change

Normalize only the integral identity π^(k+1)=π^k*π before tensoring the
original overlap. This gives a second construction on exactly the original
residue principal opens used by the retained middle transition.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R)
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "P" => WeierstrassDilatation.parameterEquiv W (π ^ (k + 1)) (π ^ k * π)
  b3 b4 b6 b3 b4 b6 (pow_succ π k) rfl rfl rfl

/-- The integral divided principal open at the actual next depth. -/
abbrev DepthDividedOpen := Localization.Away x

/-- The integral power normalization on the original divided overlap. -/
def depthDividedOpenEquiv : DepthDividedOpen W π k b3 b4 b6 ≃ₐ[R]
    DividedOpen W (π ^ k) π b3 b4 b6 :=
  PrincipalOpenTransport.equiv P _ _ (by simp only [WeierstrassDilatation.parameterEquiv_x])

/-- The actual integral depth overlap, before taking any residue fiber. -/
def depthOverlapEquiv : DepthDividedOpen W π k b3 b4 b6 ≃ₐ[R]
    XOpen W (π ^ k) π b3 b4 b6 :=
  (depthDividedOpenEquiv W π k b3 b4 b6).trans (overlapEquiv W (π ^ k) π b3 b4 b6)

/-- The integral depth overlap sends x to the inverse original incidence unit. -/
@[simp] theorem depthOverlapEquiv_x :
    depthOverlapEquiv W π k b3 b4 b6 (algebraMap _ _ x) =
      (↑(xOpenUnit W (π ^ k) π b3 b4 b6)⁻¹ : XOpen W (π ^ k) π b3 b4 b6) := by
  change overlapForward W (π ^ k) π b3 b4 b6
    (depthDividedOpenEquiv W π k b3 b4 b6 (algebraMap _ _ x)) = _
  rw [depthDividedOpenEquiv, PrincipalOpenTransport.equiv_base,
    WeierstrassDilatation.parameterEquiv_x, overlapForward_base]
  exact dividedOverlapMap_x _ _ _ _ _ _ _ _ _

/-- The integral vertical coordinate retains the original slope/incidence quotient. -/
@[simp] theorem depthOverlapEquiv_y :
    depthOverlapEquiv W π k b3 b4 b6
      (algebraMap _ _ (WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6)) =
        (↑(xOpenUnit W (π ^ k) π b3 b4 b6)⁻¹ : XOpen W (π ^ k) π b3 b4 b6) *
          algebraMap _ _ (coord W (π ^ k) π b3 b4 b6 1) := by
  change overlapForward W (π ^ k) π b3 b4 b6
    (depthDividedOpenEquiv W π k b3 b4 b6 (algebraMap _ _ _)) = _
  rw [depthDividedOpenEquiv, PrincipalOpenTransport.equiv_base,
    WeierstrassDilatation.parameterEquiv_y, overlapForward_base]
  exact dividedOverlapMap_y _ _ _ _ _ _ _ _ _

variable [IsLocalRing R]
local notation "K" => ResidueField R

/-- Tensor the integral depth overlap into the same actual residue principal opens. -/
def residueIntegralTransition : ResidueDividedOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K]
    ResidueMiddleOpen (W := W) (π := π) k b3 b4 b6 :=
  PrincipalOpenTensor.transition K x t (depthOverlapEquiv W π k b3 b4 b6)

/-- Its square retains all original integral overlap functions. -/
theorem residueIntegralTransition_coefficient (z : DepthDividedOpen W π k b3 b4 b6) :
    residueIntegralTransition W π k b3 b4 b6 (PrincipalOpenTensor.coefficient K x z) =
      PrincipalOpenTensor.coefficient K t (depthOverlapEquiv W π k b3 b4 b6 z) :=
  PrincipalOpenTensor.transition_coefficient K x t (depthOverlapEquiv W π k b3 b4 b6) z

end FLT.Mazur.WeierstrassSuccessiveX
