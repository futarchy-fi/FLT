/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedRetainedCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticMixedNearNonpunctured

/-!
# Full retained/terminal coverage near the middle stage

Cover every relatively smooth pair, including creation-zero and nonpunctured
inputs. The retained depth is unchanged or increases once. The terminal input
is unchanged. Membership names actual output domains; no gluing is asserted.
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

local notation "idx(" r ", " hr ")" => retainedOlderFormulaIndex j r hr
local notation "fr(" r ", " hr ")" => (O (idx(r, hr))).ι ≫ chart (idx(r, hr)) ≫ s
local notation "Dr(" r ", " hr ")" =>
  arithmeticRetainedTerminalOpen hπ data m j hj r j hr le_rfl (hr).le

variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ max k 1 + 2 * j)
  (h2 : W.a₂ = 0)
local notation "Dpos(" r ", " hr ", " hn ")" =>
  arithTerminalReflectedPositiveOpen node data m j hj r j hr le_rfl (hr).le
    hdepth hn (by omega : depth - r - j ≤ j) h2
local notation "Dneg(" r ", " hr ", " hn ")" =>
  arithTerminalReflectedNegativeOpen node data m j hj r j hr le_rfl (hr).le
    hdepth hn (by omega : depth - r - j ≤ j) h2

local instance arithmeticMixedNearRetained_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

include hnear in
/-- Every smooth pair in this range reaches a constructed output, with neither puncture assumed. -/
theorem arithmeticMixed_retained_near_middle_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ (r : ℕ) (hr : r < j) (z : (pullback (fr(r, hr)) fb : Scheme)),
      (r = k ∨ r = k + 1) ∧
      chart (idx(r, hr)) ((O (idx(r, hr))).ι (pullback.fst (fr(r, hr)) fb z)) =
        chart a (pullback.fst f g p) ∧
      (O b).ι (pullback.snd (fr(r, hr)) fb z) = pullback.snd f g p ∧
      (z ∈ Dr(r, hr) ∨ ∃ hn : depth ≤ r + 2 * j,
        z ∈ Dpos(r, hr, hn) ∨ z ∈ Dneg(r, hr, hn)) := by
  rcases lt_or_eq_of_le hdepth with hm | hm
  · by_cases hx : u ∈ (I (pullback.fst f g p)).asIdeal
    · have hn : depth ≤ (k + 1) + 2 * j := by omega
      obtain ⟨z, hz, he, hd⟩ := arithmeticMixed_nonpunctured_near_terminal_target
        node data m j hj k hk hdepth hn h2 hgen hm p hs ht hx
      refine ⟨k + 1, hc, z, Or.inr rfl, hz, he, ?_⟩
      rcases hd with hd | hd | hd
      · exact Or.inr ⟨hn, Or.inl hd⟩
      · exact Or.inr ⟨hn, Or.inr hd⟩
      · exact Or.inl hd
    · by_cases hk0 : k = 0
      · obtain ⟨z, hz, he, hd⟩ := arithmeticMixed_zero_horizontal_le_middle_target
          hπ data m j hj k ha node hk0 hdepth p hs ht hx
        exact ⟨k, ha, z, Or.inl rfl, congrArg (chart a) hz, he, Or.inl hd⟩
      · have hn : depth ≤ k + 2 * j := by omega
        obtain ⟨z, hz, he, hd⟩ := arithmeticMixed_horizontal_near_terminal_target
          hπ data m j hj k ha node hdepth hn h2 (by omega) hm p hs ht hx
        refine ⟨k, ha, z, Or.inl rfl, congrArg (chart a) hz, he, ?_⟩
        rcases hd with hd | hd | hd
        · exact Or.inr ⟨hn, Or.inl hd⟩
        · exact Or.inr ⟨hn, Or.inr hd⟩
        · exact Or.inl hd
  · obtain ⟨r, hr, z, hchoice, hz, he, hd⟩ := arithmeticMixed_retained_middle_target
      node data m j hj k hk hgen hm p hs ht
    exact ⟨r, hr, z, hchoice, hz, he, Or.inl hd⟩

end FLT.Mazur.WeierstrassDividedDepth
