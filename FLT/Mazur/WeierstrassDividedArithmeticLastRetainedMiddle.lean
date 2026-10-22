/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedIndexed
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleReciprocalChord

/-!
# Last-retained middle-depth transfer to constructed addition domains

The indexed incidence transfer preserves both original arithmetic inputs.
Complete middle-depth terminal coverage now supplies an actual tangent or
reciprocal chord output at its target, including the zero-abscissa case.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "I" => arithmeticRetainedTensorIso hπ data m (j + 1) hj j (Nat.lt_succ_self j)
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g" => chart 1 ≫ s
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj 1
local notation "fg" => (O).ι ≫ chart 1 ≫ s
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2

local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj
local notation "D" => arithmeticTerminalSelfSmoothTangentOpen hπ data m (j + 1) hj
local notation "F" => arithmeticTerminalSelfReciprocalChordOpen hπ data m (j + 1) hj

local instance arithmeticLastRetainedMiddle_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Indexed last-retained middle pairs reach genuine outputs with both inputs intact. -/
theorem arithmeticLastRetainedIndexed_middle_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hdepth : 2 * (j + 1) = depth)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fg fg : Scheme),
      chart 1 ((O).ι (pullback.fst fg fg z)) = chart a (pullback.fst f g p) ∧
      (O).ι (pullback.snd fg fg z) = pullback.snd f g p ∧ (z ∈ D ∨ z ∈ F) := by
  obtain ⟨z, hz, he⟩ := arithmeticLastRetainedIndexed_terminal_target
    node data m j hj hgen hdepth.le p hs ht hx
  exact ⟨z, hz, he,
    arithmeticTerminalSelf_middle_cover hπ data m (j + 1) hj node (by omega) hdepth z⟩

end FLT.Mazur.WeierstrassDividedDepth
