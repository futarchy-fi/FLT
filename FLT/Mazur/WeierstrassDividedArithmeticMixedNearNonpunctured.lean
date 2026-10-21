/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNearTerminalTarget
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage

/-!
# Nonpunctured retained inputs paired with the terminal chart

Transfer a smooth nonpunctured retained input to its next horizontal chart,
then enter one of the three actual output domains near terminal depth.
The original arithmetic inputs and quotient order are unchanged.
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
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k + 2 ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "ha" => Nat.lt_trans (Nat.lt_succ_self k) (Nat.lt_of_succ_le hk)
local notation "hc" => Nat.lt_of_succ_le hk
local notation "a" => retainedOlderFormulaIndex j k ha
local notation "c" => retainedOlderFormulaIndex j (k + 1) hc
local notation "b" => (1 : Fin (j + 3))
local notation "next" => data ⟨k + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (k + 1)).trans (hk.trans hj))⟩
local notation "Q" => Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "f" => chart a ≫ s
local notation "f'" => chart c ≫ s
local notation "g" => chart b ≫ s
local notation "fa" => (O c).ι ≫ f'
local notation "fb" => (O b).ι ≫ g
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m j hj k hk
local notation "u" => tensorCoord W (π ^ (0 + k)) π (next).b3 (next).b4 (next).b6 Q 2
local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj (k + 1) j hc le_rfl (hc).le

variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ (k + 1) + 2 * j)
  (h2 : W.a₂ = 0)
local notation "hsum" => (by omega : depth - (k + 1) - j ≤ j)
local notation "Dpos" => arithTerminalReflectedPositiveOpen node data m j hj (k + 1) j
  hc le_rfl (hc).le hdepth hnear hsum h2
local notation "Dneg" => arithTerminalReflectedNegativeOpen node data m j hj (k + 1) j
  hc le_rfl (hc).le hdepth hnear hsum h2

local instance arithmeticMixedNearNonpunctured_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Vanishing of the retained horizontal coordinate still leads to an actual mixed output. -/
theorem arithmeticMixed_nonpunctured_near_terminal_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hm : 2 * j < depth)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∈ (I (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fa fb : Scheme),
      chart c ((O c).ι (pullback.fst fa fb z)) = chart a (pullback.fst f g p) ∧
      (O b).ι (pullback.snd fa fb z) = pullback.snd f g p ∧
      (z ∈ Dpos ∨ z ∈ Dneg ∨ z ∈ D) := by
  obtain ⟨q, hq, he, hu⟩ := arithmeticFixedAdjacentPair_zero_target
    hπ data node hgen m j hj k hk g (by omega) p hs hx
  change chart c (pullback.fst f' g q) = chart a (pullback.fst f g p) at hq
  change pullback.snd f' g q = pullback.snd f g p at he
  have hs' : chart c (pullback.fst f' g q) ∈ (s).smoothLocus := by
    rw [hq]
    exact hs
  have ht' : chart b (pullback.snd f' g q) ∈ (s).smoothLocus := by
    rw [he]
    exact ht
  obtain ⟨z, hz, ht, hd⟩ := arithmeticMixed_horizontal_near_terminal_target
    hπ data m j hj (k + 1) hc node hdepth hnear h2 (by omega) hm q hs' ht' hu
  refine ⟨z, ?_, ht.trans he, hd⟩
  rw [hz]
  exact hq

end FLT.Mazur.WeierstrassDividedDepth
