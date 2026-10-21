/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNearTerminalCoverage

/-!
# Full arithmetic inputs reach the near-terminal output domains

Lift a relatively smooth pair into the smooth atlas before applying the
three-branch cover. Both original coordinates and the quotient order survive.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithTerminalReflectedPositiveOpen arithTerminalReflectedNegativeOpen
  arithmeticRetainedTerminalOpen arithmeticRetainedTerminalFormulaInput
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k < j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "next" => data ⟨k + 1, Nat.lt_succ_of_le ((Nat.succ_le_iff.mpr hk).trans hj)⟩
local notation "Q" => Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "I" => (arithmeticRetainedTensorIso hπ data m j hj k hk).inv
local notation "u" => tensorCoord W (π ^ (0 + k)) π (next).b3 (next).b4 (next).b6 Q 2

local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj k j hk le_rfl hk.le
local notation "E" => arithmeticTerminalRetainedOpen hπ data m j hj k j hk le_rfl hk.le
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s

local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k j hk le_rfl
local notation "x₂" => unequalPairRight d e
  (WeierstrassDilatation.x W (π ^ (0 + j)) (e).b3 (e).b4 (e).b6)

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)
  (hdepth : 2 * j ≤ depth) (hnear : depth ≤ k + 2 * j) (h2 : W.a₂ = 0)
local notation "hsum" => (by omega : depth - k - j ≤ j)
local notation "Dpos" => arithTerminalReflectedPositiveOpen node data m j hj k j hk le_rfl
  hk.le hdepth hnear hsum h2
local notation "Dneg" => arithTerminalReflectedNegativeOpen node data m j hj k j hk le_rfl
  hk.le hdepth hnear hsum h2
local instance arithmeticMixedNearTerminalTarget_structure :
    LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Punctured full mixed pairs reach a genuine output domain near terminal depth. -/
theorem arithmeticMixed_horizontal_near_terminal_target (hk0 : 0 < k)
    (hm : 2 * j < depth) (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∉ (I (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fa fb : Scheme),
      (O a).ι (pullback.fst fa fb z) = pullback.fst f g p ∧
      (O b).ι (pullback.snd fa fb z) = pullback.snd f g p ∧
      (z ∈ Dpos ∨ z ∈ Dneg ∨ z ∈ D) := by
  obtain ⟨z, hz, he⟩ := arithmeticAtlasRelativePair_exists hπ data m j hj a b p hs ht
  refine ⟨z, hz, he, arithmeticMixed_near_terminal_cover
    hπ data m j hj k hk node hdepth hnear h2 hk0 hm z ?_⟩
  rwa [hz]

end FLT.Mazur.WeierstrassDividedDepth
