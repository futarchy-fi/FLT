/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalAtlasInputs
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer

/-!
# The original terminal boundary in the full indexed arithmetic atlas

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
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "a" => PrincipalOpenTensor.inclusion Q t
local notation "b" => (A).hom ≫ PrincipalOpenTensor.inclusion Q x
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => (terminalArithmeticTensor_isPullback hπ data m j hj).flip
local notation "stage" => j + 1
local notation "ha" => hj
local notation "ia" => (Fin.succ ⟨stage - j, by omega⟩ : Fin (stage + 3))
local notation "ib" => (1 : Fin (stage + 3))
local notation "leftIso" => arithmeticRetainedTensorIso hπ data m stage hj j (by omega)
local notation "rightIso" => finiteDividedTensorAtlasIso hπ data Q stage hj
local notation "chart" => arithmeticTensorAtlasMap hπ data m stage ha

set_option maxHeartbeats 800000 in
-- Comparing the original tensor-ring instances is expensive during elaboration.
/-- The actual original incidence boundary, in its retained indexed source. -/
def arithmeticTerminalIndexedBoundarySource := a ≫ (leftIso).hom

/-- The actual adjacent or divided boundary, in its indexed target. -/
def arithmeticTerminalIndexedBoundaryTarget := b ≫ (rightIso).hom

instance arithmeticTerminalIndexedBoundarySource_isOpenImmersion :
    IsOpenImmersion (arithmeticTerminalIndexedBoundarySource hπ data m j hj) := by
  unfold arithmeticTerminalIndexedBoundarySource
  infer_instance

instance arithmeticTerminalIndexedBoundaryTarget_isOpenImmersion :
    IsOpenImmersion (arithmeticTerminalIndexedBoundaryTarget hπ data m j hj) := by
  unfold arithmeticTerminalIndexedBoundaryTarget
  infer_instance

/-- Both indexed boundary maps preserve every function on the arithmetic input. -/
@[reassoc] theorem arithmeticTerminalIndexedBoundary_ambient :
    arithmeticTerminalIndexedBoundarySource hπ data m j hj ≫ chart ia =
      arithmeticTerminalIndexedBoundaryTarget hπ data m j hj ≫ chart ib := by
  simp only [arithmeticTerminalIndexedBoundarySource,
    arithmeticTerminalIndexedBoundaryTarget, Category.assoc]
  rw [arithmeticBoundaryAtlas_newest, arithmeticTensorAtlas_terminal]
  simpa only [Category.assoc] using (H).w

end FLT.Mazur.WeierstrassDividedDepth
