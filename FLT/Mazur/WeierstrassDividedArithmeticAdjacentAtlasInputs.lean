/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryAtlasIndex
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentPairTransfer

/-!
# Explicit adjacent boundary inputs in the arithmetic atlas

Transport both original pair presentations to their exact tensor atlas
indices. Their full resolved arithmetic inputs agree schematically.
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
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => PolygonArithmeticStages.Quotient R π m

/-- The original older tensor isomorphism preserves its exact arithmetic atlas map. -/
@[reassoc] theorem arithmeticBoundaryAtlas_older (r : ℕ) (hr : j + 1 + r ≤ n) :
    (olderSuccessiveTensorAtlasIso hπ data Q j hj r hr).hom ≫
      arithmeticTensorAtlasMap hπ data m (j + 1 + r) hr
        (Fin.succ ⟨r + 1, by omega⟩) =
      finiteArithmeticOlderTensorChart hπ data m j hj r hr := by
  change _ ≫ ((finiteTensorAtlasMap hπ data Q (j + 1 + r) hr _ ≫ _) ≫ _) = _
  rw [← Category.assoc, olderSuccessiveTensorAtlasIso_map_assoc]
  rfl

variable (hjNext : j + 2 ≤ n) (r : ℕ) (hr : j + 2 + r ≤ n)
  (b : Fin (j + 2 + r + 3))
local notation "k" => j + 2 + r
local notation "a" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨r + 1, by omega⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hr
local notation "s" => finiteGlobalArithmeticStructure hπ data k hr m
local notation "old" => finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr
local notation "next" => finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr
local notation "g" => chart b ≫ s
local notation "O" => arithmeticAdjacentPairOpen hπ data m j hj r hr g
local notation "transfer" => arithmeticAdjacentPairTransfer hπ data m j hj hjNext r hr g

/-- The original first input, expressed at its exact retained atlas index. -/
def arithmeticAdjacentAtlasSourceFirst :=
  (O).ι ≫ pullback.fst (old ≫ s) g ≫
    (arithmeticRetainedTensorIso hπ data m k hr j (by omega)).hom

/-- The original second input is already in its chosen full tensor chart. -/
def arithmeticAdjacentAtlasSourceSecond := (O).ι ≫ pullback.snd (old ≫ s) g

/-- The transferred first input uses the actual next retained tensor isomorphism. -/
def arithmeticAdjacentAtlasTargetFirst :=
  transfer ≫ pullback.fst (next ≫ s) g ≫
    (olderSuccessiveTensorAtlasIso hπ data Q (j + 1) hjNext r hr).hom

/-- The transferred second input is the full original second input. -/
def arithmeticAdjacentAtlasTargetSecond := transfer ≫ pullback.snd (next ≫ s) g

local notation "x" => arithmeticAdjacentAtlasSourceFirst hπ data m j hj r hr b
local notation "y" => arithmeticAdjacentAtlasSourceSecond hπ data m j hj r hr b
local notation "z" => arithmeticAdjacentAtlasTargetFirst hπ data m j hj hjNext r hr b
local notation "w" => arithmeticAdjacentAtlasTargetSecond hπ data m j hj hjNext r hr b

/-- Both indexed first inputs are the same actual resolved arithmetic input. -/
theorem arithmeticAdjacentAtlasInputs_first : x ≫ chart a = z ≫ chart c := by
  simp only [arithmeticAdjacentAtlasSourceFirst, arithmeticAdjacentAtlasTargetFirst,
    Category.assoc]
  rw [arithmeticBoundaryAtlas_adjacent hπ data m j hj r hr,
    arithmeticBoundaryAtlas_older hπ data m (j + 1) hjNext r hr]
  exact (arithmeticAdjacentPairTransfer_first hπ data m j hj hjNext r hr g).symm

/-- Both indexed second inputs are identical even before passing to the ambient model. -/
theorem arithmeticAdjacentAtlasInputs_second : y = w :=
  (arithmeticAdjacentPairTransfer_second hπ data m j hj hjNext r hr g).symm

/-- The two original indexed inputs have their original common quotient coefficient point. -/
theorem arithmeticAdjacentAtlasInputs_base : x ≫ chart a ≫ s = y ≫ chart b ≫ s := by
  simp only [arithmeticAdjacentAtlasSourceFirst, arithmeticAdjacentAtlasSourceSecond,
    Category.assoc]
  rw [arithmeticBoundaryAtlas_adjacent_assoc hπ data m j hj r hr]
  exact congrArg (fun f => (O).ι ≫ f)
    (show pullback.fst (old ≫ s) g ≫ (old ≫ s) =
      pullback.snd (old ≫ s) g ≫ g from pullback.condition)

end FLT.Mazur.WeierstrassDividedDepth
