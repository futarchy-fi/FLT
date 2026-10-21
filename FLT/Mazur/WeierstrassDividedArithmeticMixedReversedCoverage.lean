/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedRetainedCoverage

/-!
# Complete mixed coverage in the terminal-first order

Swapping both the full source and the constructed smooth target preserves the
original input order. The retained factor moves by at most one creation depth.
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

local notation "Er(" r ", " hr ")" =>
  arithmeticTerminalRetainedOpen hπ data m j hj r j hr le_rfl (hr).le

local instance arithmeticMixedReversedCoverage_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data j hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth terminal/retained pair has an actual output in its original input order. -/
theorem arithmeticMixed_reversed_retained_middle_target
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hmid : 2 * j = depth)
    (p : (pullback g f : Scheme))
    (ht : chart b (pullback.fst g f p) ∈ (s).smoothLocus)
    (hs : chart a (pullback.snd g f p) ∈ (s).smoothLocus) :
    ∃ (r : ℕ) (hr : r < j) (z : (pullback fb (fr(r, hr)) : Scheme)),
      (r = k ∨ r = k + 1) ∧
      (O b).ι (pullback.fst fb (fr(r, hr)) z) = pullback.fst g f p ∧
      chart (idx(r, hr)) ((O (idx(r, hr))).ι (pullback.snd fb (fr(r, hr)) z)) =
        chart a (pullback.snd g f p) ∧ z ∈ Er(r, hr) := by
  have hs' : chart a (pullback.fst f g ((pullbackSymmetry g f).hom p)) ∈
      (s).smoothLocus := by
    rwa [SchemePairSymmetryPoints.fst_apply]
  have ht' : chart b (pullback.snd f g ((pullbackSymmetry g f).hom p)) ∈
      (s).smoothLocus := by
    rwa [SchemePairSymmetryPoints.snd_apply]
  obtain ⟨r, hr, z, hkr, hz, he, hd⟩ := arithmeticMixed_retained_middle_target
    node data m j hj k hk hgen hmid ((pullbackSymmetry g f).hom p) hs' ht'
  rw [SchemePairSymmetryPoints.fst_apply] at hz
  rw [SchemePairSymmetryPoints.snd_apply] at he
  refine ⟨r, hr, (pullbackSymmetry (fr(r, hr)) fb).hom z, hkr, ?_, ?_, ?_⟩
  · rwa [SchemePairSymmetryPoints.fst_apply]
  · rwa [SchemePairSymmetryPoints.snd_apply]
  · change (pullbackSymmetry fb (fr(r, hr))).hom
      ((pullbackSymmetry (fr(r, hr)) fb).hom z) ∈ Dr(r, hr)
    have hi := congrArg (fun morphism => morphism z)
      (pullbackSymmetry (fr(r, hr)) fb).hom_inv_id
    change (pullbackSymmetry fb (fr(r, hr))).hom
      ((pullbackSymmetry (fr(r, hr)) fb).hom z) = z at hi
    rwa [hi]

end FLT.Mazur.WeierstrassDividedDepth
