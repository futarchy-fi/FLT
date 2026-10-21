/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialTerminalAddition
public import FLT.Mazur.WeierstrassDividedArithmeticMixedAllMiddleCoverage
public import FLT.Mazur.WeierstrassDividedUnequalDepthZeroNodalCoverage

/-!
# Punctured zero-depth mixed coverage at every arithmetic order

Both the retained initial chart and the creation-depth-zero older chart
have constructed outputs with a full-depth punctured nodal terminal input.
No terminal contraction or residue branch choice is used. Combining with
the middle-depth result covers all positive terminal depths up to the middle.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedInitialFormulaCoordinates retainedOlderLowerCoordinates retainedOlderFormulaIndex
  terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {depth n : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (hj0 : 0 < j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "b" => (1 : Fin (j + 3))
local notation "Q" => Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "x₁" => unequalPairLeft d e (x W (π ^ (0 + 0)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => unequalPairRight d e (x W (π ^ (0 + j)) (e).b3 (e).b4 (e).b6)

section Initial
include hj0
local notation "a" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "input" => arithmeticInitialTerminalFormulaInput hπ data m j hj
local notation "D" => arithmeticInitialTerminalOpen hπ data m j hj
local notation "swap" => (pullbackSymmetry fb fa).hom
local notation "E" => arithmeticTerminalInitialOpen hπ data m j hj

/-- The original initial/terminal pair is covered at every strict pre-middle terminal depth. -/
theorem arithmeticInitialTerminalOpen_nodal_mem (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal) : p ∈ D :=
  unequalDepthDomain_zero_nodal_mem node d e (Nat.zero_le _) data
    (by change (0 + j) - (0 + 0) ≤ n; omega) (unequalPairLeft d e) (unequalPairRight d e)
    rfl (by change 0 < 0 + j; omega) (by change 2 * (0 + j) < depth; omega) (input p)
    (arithmeticInitialTerminalFormulaInput_parameter_mem hπ data m j hj p) hx hu

/-- All positive terminal depths up to the middle are covered for punctured initial pairs. -/
theorem arithmeticInitialTerminalOpen_le_middle_mem (hm : 2 * j ≤ depth)
    (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal) : p ∈ D := by
  rcases lt_or_eq_of_le hm with h | h
  · exact arithmeticInitialTerminalOpen_nodal_mem node data m j hj hj0 h p hx hu
  · exact arithmeticInitialTerminalOpen_middle_mem hπ data m j hj node hj0 h p hx

/-- The reverse original order has the same coverage, including odd node depths. -/
theorem arithmeticTerminalInitialOpen_le_middle_mem (hm : 2 * j ≤ depth)
    (p : (pullback fb fa : Scheme))
    (hx : x₁ ∉ (input (swap p)).asIdeal) (hu : x₂ ∉ (input (swap p)).asIdeal) : p ∈ E :=
  arithmeticInitialTerminalOpen_le_middle_mem node data m j hj hj0 hm (swap p) hx hu
end Initial

section Older
local notation "a" => retainedOlderFormulaIndex j 0 hj0
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj 0 j hj0 le_rfl
local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj 0 j hj0 le_rfl (Nat.zero_le _)
local notation "swap" => (pullbackSymmetry fb fa).hom
local notation "E" => arithmeticTerminalRetainedOpen hπ data m j hj 0 j hj0 le_rfl (Nat.zero_le _)

/-- Creation-depth-zero retained inputs also have branch-free pre-middle terminal coverage. -/
theorem arithmeticZeroRetainedTerminalOpen_nodal_mem (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal) : p ∈ D :=
  unequalDepthDomain_zero_nodal_mem node d e (Nat.zero_le _) data
    (by change (0 + j) - (0 + 0) ≤ n; omega) (unequalPairLeft d e) (unequalPairRight d e)
    rfl (by change 0 < 0 + j; omega) (by change 2 * (0 + j) < depth; omega) (input p)
    (arithmeticRetainedTerminalFormulaInput_parameter_mem hπ data m j hj 0 j hj0 le_rfl p) hx hu

/-- The entire positive range up to middle depth is covered for punctured zero-created pairs. -/
theorem arithmeticZeroRetainedTerminalOpen_le_middle_mem (hm : 2 * j ≤ depth)
    (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal) : p ∈ D := by
  rcases lt_or_eq_of_le hm with h | h
  · exact arithmeticZeroRetainedTerminalOpen_nodal_mem node data m j hj hj0 h p hx hu
  · exact arithmeticMixed_all_middle_mem hπ data m j hj 0 hj0 node h p hx

/-- Reversing the zero-created and terminal inputs preserves the same actual coverage. -/
theorem arithmeticTerminalZeroRetainedOpen_le_middle_mem (hm : 2 * j ≤ depth)
    (p : (pullback fb fa : Scheme))
    (hx : x₁ ∉ (input (swap p)).asIdeal) (hu : x₂ ∉ (input (swap p)).asIdeal) : p ∈ E :=
  arithmeticZeroRetainedTerminalOpen_le_middle_mem node data m j hj hj0 hm (swap p) hx hu
end Older

end FLT.Mazur.WeierstrassDividedDepth
