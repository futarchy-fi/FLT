/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalIntersection
public import FLT.Mazur.WeierstrassSuccessiveArithmeticBranchBoundary

/-!
# Constructed polygon branches on the original terminal arithmetic boundary

The complete left Laurent open of each constructed polygon branch is its
exact intersection with the original divided arithmetic chart. The boundary
map uses the original depth transition on all functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) (opposite : Bool)
local notation "c" => arithmeticTensorBranchChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "b" => arithmeticBranchLeftBoundary π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite

/-- The constructed branch's whole Laurent boundary uses the original depth transition. -/
def terminalArithmeticBranchBoundary : PolygonSmoothing.branchTorus Q ⟶
    Spec (.of (WeierstrassDilatation.ScalarExtension W (π ^ (start + j + 1))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)) :=
  b ≫ (PrincipalOpenTensor.transitionIso Q x t a).hom ≫ PrincipalOpenTensor.inclusion Q x

/-- The actual divided chart meets each polygon branch in its full original left torus. -/
theorem terminalArithmeticBranch_isPullback :
    IsPullback (terminalArithmeticBranchBoundary data m j hj ha hs h2 h3 h4 h6 opposite)
      (PolygonSmoothing.leftBranchOpen Q (parameter R π m))
      (finiteArithmeticDividedTensorChart hπ data m (j + 1) hj)
      (c ≫ finiteArithmeticNewestTensorChart hπ data m j hj) :=
  (arithmeticBranchLeftBoundary_isPullback π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite).paste_horiz
      (terminalArithmeticTensor_isPullback hπ data m j hj)

/-- The terminal boundary comparison commutes in the actual global arithmetic stage. -/
@[reassoc] theorem terminalArithmeticBranchBoundary_chart :
    terminalArithmeticBranchBoundary data m j hj ha hs h2 h3 h4 h6 opposite ≫
      finiteArithmeticDividedTensorChart hπ data m (j + 1) hj =
        PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫
          c ≫ finiteArithmeticNewestTensorChart hπ data m j hj :=
  (terminalArithmeticBranch_isPullback hπ data m j hj ha hs h2 h3 h4 h6 opposite).w

/-- The original terminal polygon torus is isomorphic to the actual chart intersection. -/
def terminalArithmeticBranchPullbackIso :=
  (terminalArithmeticBranch_isPullback hπ data m j hj ha hs h2 h3 h4 h6 opposite).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
