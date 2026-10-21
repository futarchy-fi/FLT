/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryAtlasIndex
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPairTransfer

/-!
# Explicit terminal boundary inputs in the arithmetic atlas

The original newest successive input and terminal divided output use their
actual tensor isomorphisms. Both resolved arithmetic inputs are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (b : Fin (j + 1 + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "a" => (Fin.succ ⟨j + 1 - j, by omega⟩ : Fin (j + 1 + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "g" => chart b ≫ s
local notation "O" => arithmeticTerminalPairOpen hπ data m j hj g
local notation "transfer" => arithmeticTerminalPairTransfer hπ data m j hj g

/-- The original first input at its exact newest retained atlas index. -/
def arithmeticTerminalAtlasSourceFirst :=
  (O).ι ≫ pullback.fst (old ≫ s) g ≫
    (arithmeticRetainedTensorIso hπ data m (j + 1) hj j (by omega)).hom

/-- The complete original second indexed chart input. -/
def arithmeticTerminalAtlasSourceSecond := (O).ι ≫ pullback.snd (old ≫ s) g

/-- The actual terminal transfer followed by the original divided tensor isomorphism. -/
def arithmeticTerminalAtlasTargetFirst :=
  transfer ≫ pullback.fst (next ≫ s) g ≫
    (finiteDividedTensorAtlasIso hπ data Q (j + 1) hj).hom

/-- The complete second input of the terminal boundary transfer. -/
def arithmeticTerminalAtlasTargetSecond := transfer ≫ pullback.snd (next ≫ s) g

local notation "x" => arithmeticTerminalAtlasSourceFirst hπ data m j hj b
local notation "y" => arithmeticTerminalAtlasSourceSecond hπ data m j hj b
local notation "z" => arithmeticTerminalAtlasTargetFirst hπ data m j hj b
local notation "w" => arithmeticTerminalAtlasTargetSecond hπ data m j hj b

/-- The terminal indexed first input agrees with the original resolved arithmetic input. -/
theorem arithmeticTerminalAtlasInputs_first : x ≫ chart a = z ≫ chart 1 := by
  simp only [arithmeticTerminalAtlasSourceFirst, arithmeticTerminalAtlasTargetFirst,
    Category.assoc]
  rw [arithmeticBoundaryAtlas_newest hπ data m j hj,
    arithmeticTensorAtlas_terminal hπ data m (j + 1) hj]
  exact (arithmeticTerminalPairTransfer_first hπ data m j hj g).symm

/-- The second input is exactly preserved by the terminal change of coordinates. -/
theorem arithmeticTerminalAtlasInputs_second : y = w :=
  (arithmeticTerminalPairTransfer_second hπ data m j hj g).symm

/-- Both original inputs retain their actual common arithmetic coefficient morphism. -/
theorem arithmeticTerminalAtlasInputs_base : x ≫ chart a ≫ s = y ≫ chart b ≫ s := by
  simp only [arithmeticTerminalAtlasSourceFirst, arithmeticTerminalAtlasSourceSecond,
    Category.assoc]
  rw [arithmeticBoundaryAtlas_newest_assoc hπ data m j hj]
  exact congrArg (fun f => (O).ι ≫ f)
    (show pullback.fst (old ≫ s) g ≫ (old ≫ s) =
      pullback.snd (old ≫ s) g ≫ g from pullback.condition)

end FLT.Mazur.WeierstrassDividedDepth
