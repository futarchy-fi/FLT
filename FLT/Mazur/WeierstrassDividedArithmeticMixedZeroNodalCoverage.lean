/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedHorizontalCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticMixedTerminalPuncture
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSmoothPuncture
public import FLT.Mazur.WeierstrassDividedArithmeticZeroMixedCoverage

/-!
# Full-depth terminal punctures and zero-created mixed nodal coverage

Relative smoothness forces the terminal puncture below middle depth. A
horizontally punctured creation-zero retained input therefore reaches the
actual addition domain throughout the positive range up to middle depth.
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

/-- Any full smooth mixed pair supplies its own terminal puncture below middle depth. -/
theorem arithmeticMixedFormulaInput_nodal_terminal_punctured [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme)) : x₂ ∉ (input p).asIdeal := by
  rw [arithmeticMixedFormulaInput_terminal_x_iff]
  exact arithmeticTerminalTensor_nodal_punctured hπ data m j hj node
    (by omega) (by omega) _ (pullback.snd fa fb p).property

/-- Creation-zero retained pairs need only their original horizontal puncture. -/
theorem arithmeticMixed_zero_horizontal_le_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hk0 : k = 0) (hm : 2 * j ≤ depth)
    (p : (pullback fa fb : Scheme))
    (hx : u ∉ (I ((O a).ι (pullback.fst fa fb p))).asIdeal) : p ∈ D := by
  subst k
  rcases lt_or_eq_of_le hm with h | h
  · exact arithmeticZeroRetainedTerminalOpen_nodal_mem node data m j hj hk h p
      (fun hz => hx ((arithmeticMixedFormulaInput_x_iff
        hπ data m j hj 0 j hk le_rfl p).mp hz))
      (arithmeticMixedFormulaInput_nodal_terminal_punctured hπ data m j hj 0 hk node h p)
  · exact arithmeticMixed_horizontal_middle_mem hπ data m j hj 0 hk node h p hx

/-- The reversed original pair keeps the same creation-zero retained coordinate. -/
theorem arithmeticMixed_reversed_zero_horizontal_le_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hk0 : k = 0) (hm : 2 * j ≤ depth)
    (p : (pullback fb fa : Scheme))
    (hx : u ∉ (I ((O a).ι (pullback.snd fb fa p))).asIdeal) : p ∈ E := by
  apply arithmeticMixed_zero_horizontal_le_middle_mem hπ data m j hj k hk node hk0 hm
    ((pullbackSymmetry fb fa).hom p)
  rwa [SchemePairSymmetryPoints.fst_apply]

local instance arithmeticMixedZeroNodalCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Original relatively smooth inputs lift to the covered domain with both coordinates intact. -/
theorem arithmeticMixed_zero_horizontal_le_middle_target [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hk0 : k = 0) (hm : 2 * j ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∉ (I (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fa fb : Scheme),
      (O a).ι (pullback.fst fa fb z) = pullback.fst f g p ∧
      (O b).ι (pullback.snd fa fb z) = pullback.snd f g p ∧ z ∈ D := by
  obtain ⟨z, hz, he⟩ := arithmeticAtlasRelativePair_exists hπ data m j hj a b p hs ht
  refine ⟨z, hz, he, arithmeticMixed_zero_horizontal_le_middle_mem
    hπ data m j hj k hk node hk0 hm z ?_⟩
  rwa [hz]

end FLT.Mazur.WeierstrassDividedDepth
