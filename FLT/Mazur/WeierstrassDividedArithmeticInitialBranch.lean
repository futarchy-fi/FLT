/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialIntersection
public import FLT.Mazur.WeierstrassSuccessiveArithmeticBranchBoundary

/-!
# Constructed polygon branches on the initial retained arithmetic boundary

The original right Laurent open of either constructed branch is exactly its
intersection with the initial chart, at every later retention depth. Its
map retains both original integral overlap transitions after base change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonArithmeticStages
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m : ℕ)
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t a
local notation "B" => PrincipalOpenTensor.transitionIso Q x u b

/-- Reorient the full initial tensor intersection using its successive boundary coordinate. -/
theorem initialArithmeticRightTensor_isPullback :
    IsPullback ((B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion Q t)
      (PrincipalOpenTensor.inclusion Q u)
      (finiteArithmeticInitialTensorChart hπ data m (1 + r) hr)
      (finiteArithmeticOlderTensorChart hπ data m 0 h1 r hr) := by
  exact (initialArithmeticTensor_isPullback hπ data m h1 r hr).of_iso
    (B).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ start) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b3)
  (h4 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b4)
  (h6 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b6) (opposite : Bool)
local notation "c" => WeierstrassSuccessiveX.arithmeticTensorBranchChart π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite
local notation "β" => WeierstrassSuccessiveX.arithmeticBranchRightBoundary π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite

/-- The initial branch boundary retains the actual two original tensor overlap maps. -/
def initialArithmeticBranchBoundary : PolygonSmoothing.branchTorus Q ⟶
    Spec (.of (WeierstrassModificationX.ScalarExtension W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)) :=
  β ≫ (B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion Q t

/-- The full right polygon torus is exactly the intersection with the initial arithmetic chart. -/
theorem initialArithmeticBranch_isPullback :
    IsPullback (initialArithmeticBranchBoundary hπ data m h1 ha hs h2 h3 h4 h6 opposite)
      (PolygonSmoothing.rightBranchOpen Q (parameter R π m))
      (finiteArithmeticInitialTensorChart hπ data m (1 + r) hr)
      (c ≫ finiteArithmeticOlderTensorChart hπ data m 0 h1 r hr) :=
  (WeierstrassSuccessiveX.arithmeticBranchRightBoundary_isPullback π m W (π ^ start)
    (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 h3 h4 h6 opposite).paste_horiz
      (initialArithmeticRightTensor_isPullback hπ data m h1 r hr)

/-- The constructed initial boundary square commutes in every retained arithmetic stage. -/
@[reassoc] theorem initialArithmeticBranchBoundary_chart :
    initialArithmeticBranchBoundary hπ data m h1 ha hs h2 h3 h4 h6 opposite ≫
      finiteArithmeticInitialTensorChart hπ data m (1 + r) hr =
        PolygonSmoothing.rightBranchOpen Q (parameter R π m) ≫
          c ≫ finiteArithmeticOlderTensorChart hπ data m 0 h1 r hr :=
  (initialArithmeticBranch_isPullback hπ data m h1 r hr ha hs h2 h3 h4 h6 opposite).w

/-- The original initial Laurent boundary is the whole actual arithmetic fiber product. -/
def initialArithmeticBranchPullbackIso :=
  (initialArithmeticBranch_isPullback hπ data m h1 r hr ha hs h2 h3 h4 h6 opposite).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
