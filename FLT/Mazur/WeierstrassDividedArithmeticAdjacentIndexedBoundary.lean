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
# The original adjacent boundary in the full indexed arithmetic atlas

Both boundary maps retain the original tensor intersection and are open
immersions. Their full resolved arithmetic inputs agree schematically.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  PrincipalOpenTensor.transitionIso TensorProduct
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "eNext" => data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩
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
local notation "old" => finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr
local notation "next" => finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 2 + r) hr m
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => adjacentArithmeticTensor_isPullback hπ data m j hj hjNext r hr
local notation "stage" => j + 2 + r
local notation "ha" => hr
local notation "ia" => (Fin.succ ⟨stage - j, by omega⟩ : Fin (stage + 3))
local notation "ib" => (Fin.succ ⟨r + 1, by omega⟩ : Fin (stage + 3))
local notation "leftIso" => arithmeticRetainedTensorIso hπ data m stage hr j (by omega)
local notation "rightIso" => olderSuccessiveTensorAtlasIso hπ data Q (j + 1) hjNext r hr
local notation "chart" => arithmeticTensorAtlasMap hπ data m stage ha

set_option maxHeartbeats 800000 in
-- Comparing the original tensor-ring instances is expensive during elaboration.
/-- The actual original incidence boundary, in its retained indexed source. -/
def arithmeticAdjacentIndexedBoundarySource := a ≫ (leftIso).hom

/-- The actual adjacent or divided boundary, in its indexed target. -/
def arithmeticAdjacentIndexedBoundaryTarget := b ≫ (rightIso).hom

instance arithmeticAdjacentIndexedBoundarySource_isOpenImmersion :
    IsOpenImmersion (arithmeticAdjacentIndexedBoundarySource hπ data m j hj r hr) := by
  unfold arithmeticAdjacentIndexedBoundarySource
  infer_instance

instance arithmeticAdjacentIndexedBoundaryTarget_isOpenImmersion :
    IsOpenImmersion (arithmeticAdjacentIndexedBoundaryTarget hπ data m j hj hjNext r hr) := by
  unfold arithmeticAdjacentIndexedBoundaryTarget
  infer_instance

/-- Both indexed boundary maps preserve every function on the arithmetic input. -/
@[reassoc] theorem arithmeticAdjacentIndexedBoundary_ambient :
    arithmeticAdjacentIndexedBoundarySource hπ data m j hj r hr ≫ chart ia =
      arithmeticAdjacentIndexedBoundaryTarget hπ data m j hj hjNext r hr ≫ chart ib := by
  simp only [arithmeticAdjacentIndexedBoundarySource,
    arithmeticAdjacentIndexedBoundaryTarget, Category.assoc]
  rw [arithmeticBoundaryAtlas_adjacent, arithmeticBoundaryAtlas_older]
  simpa only [Category.assoc] using (H).w

end FLT.Mazur.WeierstrassDividedDepth
