/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedCoverage
public import FLT.Mazur.WeierstrassDividedUnequalDepthZeroMiddleCoverage

/-!
# Mixed arithmetic coverage at the exact middle terminal depth

Keep the terminal coordinates at their full final depth. Every punctured
retained input, including creation depth zero, then has a constructed difference-depth
output in both input orders. No terminal puncture, opposite-branch choice,
or sum-depth bound is required.
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
  retainedOlderLowerCoordinates retainedOlderFormulaIndex terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k < j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
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
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k j hk le_rfl

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj k j hk le_rfl hk.le
local notation "swap" => (pullbackSymmetry fb fa).hom
local notation "E" => arithmeticTerminalRetainedOpen hπ data m j hj k j hk le_rfl hk.le

/-- Middle-depth mixed inputs are covered using only puncturing of the retained factor. -/
theorem arithmeticMixed_all_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hmid : 2 * j = depth)
    (p : (pullback fa fb : Scheme)) (hx : x₁ ∉ (input p).asIdeal) : p ∈ D := by
  exact unequalDepthDomain_all_middle_mem node d e (Nat.add_le_add_left hk.le 0)
    data (by change (0 + j) - (0 + k) ≤ n; omega) al ar
    (by change 0 + k < 0 + j; omega)
    (by change 2 * (0 + j) = depth; omega) (input p)
    (arithmeticRetainedTerminalFormulaInput_parameter_mem hπ data m j hj k j hk le_rfl p) hx

/-- The reverse original input order has the same coverage without a terminal puncture. -/
theorem arithmeticMixed_reversed_all_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hmid : 2 * j = depth)
    (p : (pullback fb fa : Scheme)) (hx : x₁ ∉ (input (swap p)).asIdeal) : p ∈ E :=
  arithmeticMixed_all_middle_mem hπ data m j hj k hk node hmid (swap p) hx

/-- The punctured retained-factor open in the entire original arithmetic mixed pair. -/
def arithmeticMixedAllMiddlePuncturedOpen : (pullback fa fb).Opens :=
  input ⁻¹ᵁ PrimeSpectrum.basicOpen x₁

/-- The existing difference-depth output covers the whole retained-punctured mixed open. -/
theorem arithmeticMixedAllMiddlePuncturedOpen_le [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hmid : 2 * j = depth) :
    arithmeticMixedAllMiddlePuncturedOpen hπ data m j hj k hk ≤ D := by
  intro p hp
  exact arithmeticMixed_all_middle_mem hπ data m j hj k hk node hmid p hp

end FLT.Mazur.WeierstrassDividedDepth
