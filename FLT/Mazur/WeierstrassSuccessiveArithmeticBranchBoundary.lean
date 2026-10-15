/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches
public import FLT.Mazur.WeierstrassSuccessiveTensorSlopeBoundary

/-!
# Exact Laurent boundaries of both original arithmetic polygon branches

At every arithmetic order, the original left and right polygon torus opens
are precisely the inverse images of the original tensor boundary opens.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

variable (opposite : Bool)
local notation "v" => arithmeticBranchSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite
local notation "hv" => arithmeticBranchSlope_equation π m W s b3 b4 b6
  ha hs h2 h3 h4 h6 opposite
local notation "c" => arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite

/-- The full original left torus on either constructed arithmetic branch. -/
def arithmeticBranchLeftBoundary : PolygonSmoothing.branchTorus Q ⟶
    Spec (.of (Localization.Away (tensorCoord W s π b3 b4 b6 Q 0))) :=
  tensorSlopeLeftBoundary W s π b3 b4 b6 Q v hv

/-- The left Laurent open is the exact original arithmetic tensor intersection. -/
theorem arithmeticBranchLeftBoundary_isPullback :
    IsPullback (arithmeticBranchLeftBoundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)
      (PolygonSmoothing.leftBranchOpen Q (parameter R π m))
      (PrincipalOpenTensor.inclusion Q (coord W s π b3 b4 b6 0)) c := by
  have H := tensorSlopeLeftBoundary_isPullback W s π b3 b4 b6 Q v hv
  rw [arithmeticTensorBranchChart_eq] at H
  exact H

/-- Both constructed branches retain the original left tensor-boundary restriction. -/
@[reassoc] theorem arithmeticBranchLeftBoundary_inclusion :
    arithmeticBranchLeftBoundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite ≫
      PrincipalOpenTensor.inclusion Q (coord W s π b3 b4 b6 0) =
        PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫ c :=
  (arithmeticBranchLeftBoundary_isPullback π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite).w

/-- The full original right torus on either constructed arithmetic branch. -/
def arithmeticBranchRightBoundary : PolygonSmoothing.branchTorus Q ⟶
    Spec (.of (Localization.Away (tensorCoord W s π b3 b4 b6 Q 2))) :=
  tensorSlopeRightBoundary W s π b3 b4 b6 Q v hv

/-- The right Laurent open is the exact original arithmetic tensor intersection. -/
theorem arithmeticBranchRightBoundary_isPullback :
    IsPullback (arithmeticBranchRightBoundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)
      (PolygonSmoothing.rightBranchOpen Q (parameter R π m))
      (PrincipalOpenTensor.inclusion Q (coord W s π b3 b4 b6 2)) c := by
  have H := tensorSlopeRightBoundary_isPullback W s π b3 b4 b6 Q v hv
  rw [arithmeticTensorBranchChart_eq] at H
  exact H

/-- Both constructed branches retain the original right tensor-boundary restriction. -/
@[reassoc] theorem arithmeticBranchRightBoundary_inclusion :
    arithmeticBranchRightBoundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite ≫
      PrincipalOpenTensor.inclusion Q (coord W s π b3 b4 b6 2) =
        PolygonSmoothing.rightBranchOpen Q (parameter R π m) ≫ c :=
  (arithmeticBranchRightBoundary_isPullback π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite).w

end FLT.Mazur.WeierstrassSuccessiveX
