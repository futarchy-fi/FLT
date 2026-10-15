/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialComparison
public import FLT.Mazur.WeierstrassModificationXArithmeticNodeBoundary

/-!
# Both full initial nodes retain the original adjacent arithmetic transitions

The independently constructed full-node restrictions agree with the original
right boundary and both original tensor transition isomorphisms, for each label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1)) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ k) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ d.b3) (hd4 : π ∣ d.b4) (hd6 : π ∣ d.b6)
  (he3 : π ∣ e.b3) (he4 : π ∣ e.b4) (he6 : π ∣ e.b6)
local notation "Q" => Quotient R π m
local notation "v₁" => arithmeticBranchSlope π m W (π ^ k) (Data.b3 e) (Data.b4 e)
  (Data.b6 e) ha hs h2 he3 he4 he6
local notation "hv₁" => arithmeticBranchSlope_equation π m W (π ^ k) (Data.b3 e) (Data.b4 e)
  (Data.b6 e) ha hs h2 he3 he4 he6
local notation "x" => WeierstrassDilatation.x W (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t₀" => t W (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u₁" => coord W (π ^ k) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "a" => overlapEquiv W (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "G" => arithmeticInitialNodeRestriction π m W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6 hs

/-- The first full node restricts to the exact original small adjacent-order boundary. -/
@[reassoc] theorem arithmeticInitialFullNode_boundary :
    G ≫ arithmeticInitialTensorNodeChart π m W (π ^ k)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6 =
        tensorSlopeRightBoundary W (π ^ k) π e.b3 e.b4 e.b6 Q (v₁ false) (hv₁ false) ≫
          (PrincipalOpenTensor.transitionIso Q x u₁ b).hom ≫
            (PrincipalOpenTensor.transitionIso Q x t₀ a).inv ≫
              PrincipalOpenTensor.inclusion Q t₀ := by
  rw [arithmeticInitialTensorNode_boundary]
  exact arithmeticInitialTensor_boundary hπ d e m ha hs h2 hd3 hd4 hd6 he3 he4 he6 false

/-- The opposite full node restricts to the exact original opposite adjacent-order boundary. -/
@[reassoc] theorem arithmeticOppositeInitialFullNode_boundary :
    G ≫ arithmeticOppositeInitialTensorNodeChart π m W (π ^ k)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6 =
        tensorSlopeRightBoundary W (π ^ k) π e.b3 e.b4 e.b6 Q (v₁ true) (hv₁ true) ≫
          (PrincipalOpenTensor.transitionIso Q x u₁ b).hom ≫
            (PrincipalOpenTensor.transitionIso Q x t₀ a).inv ≫
              PrincipalOpenTensor.inclusion Q t₀ := by
  rw [arithmeticOppositeInitialTensorNode_boundary]
  exact arithmeticInitialTensor_boundary hπ d e m ha hs h2 hd3 hd4 hd6 he3 he4 he6 true

end FLT.Mazur.WeierstrassDividedDepth
