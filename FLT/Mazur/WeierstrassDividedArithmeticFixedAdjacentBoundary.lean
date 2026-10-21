/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentAtlasInputs
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Adjacent boundary maps at a fixed arbitrary arithmetic stage

Both original tensor boundaries are placed at one common stage, indexed by
creation depth. Independent depths can now share the same pair construction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
open scoped TensorProduct
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  PrincipalOpenTensor.transitionIso TensorProduct
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (j : ℕ) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, by omega⟩
local notation "eNext" => data ⟨j + 2, by omega⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) 2
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso Q x u (previousBoundaryEquiv hπ e eNext)
local notation "a" => (A).inv ≫ PrincipalOpenTensor.inclusion Q t
local notation "b" => (B).inv ≫ PrincipalOpenTensor.inclusion Q u
local notation "ia" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "ib" => (Fin.succ ⟨k - (j + 1), by omega⟩ : Fin (k + 3))
local notation "leftIso" => arithmeticRetainedTensorIso hπ data m k hk j (by omega)
local notation "rightIso" => arithmeticRetainedTensorIso hπ data m k hk (j + 1) (by omega)
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk

set_option maxHeartbeats 800000 in
-- Comparing the original tensor-ring instances is expensive during elaboration.
/-- The actual original incidence boundary, in its retained indexed source. -/
def arithmeticFixedAdjacentBoundarySource :
    Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] x)))
      ⟶ globalTensorAtlasObject hπ data Q k hk ia := a ≫ (leftIso).hom

set_option maxHeartbeats 800000 in
-- Compare the original next-chart tensor-ring instances without unfolding their quotient.
/-- The actual next retained boundary, in its indexed target. -/
def arithmeticFixedAdjacentBoundaryTarget :
    Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] x)))
      ⟶ globalTensorAtlasObject hπ data Q k hk ib := b ≫ (rightIso).hom

instance arithmeticFixedAdjacentBoundarySource_isOpenImmersion :
    IsOpenImmersion (arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj) := by
  unfold arithmeticFixedAdjacentBoundarySource
  infer_instance

instance arithmeticFixedAdjacentBoundaryTarget_isOpenImmersion :
    IsOpenImmersion (arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj) := by
  unfold arithmeticFixedAdjacentBoundaryTarget
  infer_instance

attribute [local irreducible] arithmeticFixedAdjacentBoundarySource
  arithmeticFixedAdjacentBoundaryTarget arithmeticRetainedTensorChart

set_option maxHeartbeats 800000 in
-- Reindexing the original tensor maps requires extra elaboration for the ring instances.
/-- Both indexed boundary maps preserve every function on the arithmetic input. -/
@[reassoc] theorem arithmeticFixedAdjacentBoundary_ambient :
    arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj ≫ chart ia =
      arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj ≫ chart ib := by
  simp only [arithmeticFixedAdjacentBoundarySource,
    arithmeticFixedAdjacentBoundaryTarget, Category.assoc]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [arithmeticBoundaryAtlas_adjacent hπ data m j (by omega) r hk]
  have he := arithmeticRetainedTensorChart_eq hπ data m (j + 2 + r) hk
    (j + 1) (by omega) r hk
  unfold arithmeticRetainedTensorChart at he
  rw [he]
  simpa only [Category.assoc] using
    (adjacentArithmeticTensor_isPullback hπ data m j (by omega) (by omega) r hk).w

end FLT.Mazur.WeierstrassDividedDepth
