/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedCoverage
public import FLT.Mazur.WeierstrassDividedTerminalLowerClosedFiber

/-!
# Punctured arithmetic terminal coordinates must keep their final depth

The statement concerns the original full smooth arithmetic pair. Its
terminal input cannot be made punctured by strict coordinate lowering.
Consequently the positive sum-depth bound is incompatible with punctured
terminal coordinates at every arithmetic quotient order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k l hk hl

local notation "z" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "B" => Coordinate W (π ^ (0 + j)) (z).b3 (z).b4 (z).b6
local notation "C" => Coordinate W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6
local notation "ar" => unequalPairRight d e
local notation "right" => Spec.map (CommRingCat.ofHom (ar).toRingHom)
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "low" => terminalLowerCoordinates hπ data j hj l hl
local notation "trans" => depthTransition π (0 + l) (0 + j) hπ
  (Nat.add_le_add_left hl 0) W (e).b3 (e).b4 (e).b6 (z).b3 (z).b4 (z).b6
  (e).factor3 (e).factor4 (e).factor6 (z).factor3 (z).factor4 (z).factor6
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)

/-- Lowered terminal abscissae vanish on every original arithmetic pair. -/
theorem arithmeticMixed_terminal_lower_mem (hlt : l < j) (p : (pullback fa fb : Scheme)) :
    x₂ ∈ (input p).asIdeal := by
  let prime : PrimeSpectrum B := (pullback.snd fa fb ≫ (O b).ι ≫ coords b) p
  have heq : right (input p) = low prime := by
    exact congrArg (fun f : pullback fa fb ⟶ Spec (.of C) => f p)
      (arithmeticRetainedTerminalFormulaInput_right hπ data m j hj k l hk hl)
  have hp : algebraMap R C π ∈ (right (input p)).asIdeal := by
    change ar (algebraMap R C π) ∈ (input p).asIdeal
    simpa only [AlgHom.commutes] using
      arithmeticRetainedTerminalFormulaInput_parameter_mem hπ data m j hj k l hk hl p
  rw [heq] at hp
  change trans (algebraMap R C π) ∈ prime.asIdeal at hp
  have hq : algebraMap R B π ∈ prime.asIdeal := by
    simpa only [AlgHom.commutes] using hp
  change x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6 ∈ (right (input p)).asIdeal
  rw [heq]
  exact (terminalLowerCoordinates_closedFiber hπ data j hj l hl hlt prime hq).1

/-- Punctured terminal coordinates on an actual arithmetic pair retain the final depth. -/
theorem arithmeticMixed_terminal_punctured_depth (p : (pullback fa fb : Scheme))
    (hx : x₂ ∉ (input p).asIdeal) : l = j := by
  by_contra h
  exact hx (arithmeticMixed_terminal_lower_mem hπ data m j hj k l hk hl (by omega) p)

/-- A positive sum-depth range cannot supply punctured terminal inputs on the closed fiber. -/
theorem arithmeticMixed_sumDepth_terminal_mem (hk0 : 0 < k) (hsum : k + l ≤ j)
    (p : (pullback fa fb : Scheme)) : x₂ ∈ (input p).asIdeal :=
  arithmeticMixed_terminal_lower_mem hπ data m j hj k l hk hl (by omega) p

end FLT.Mazur.WeierstrassDividedDepth
