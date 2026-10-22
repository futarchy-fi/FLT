/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNodalReflectedOutput
public import FLT.Mazur.WeierstrassDividedArithmeticMixedZeroNodalCoverage
public import FLT.Mazur.WeierstrassDividedUnequalDepthZeroMiddleCoverage

/-!
# Coverage of normalized retained/terminal formula domains

For a smooth terminal input before the middle, its horizontal coordinate is
already nonzero. Only the retained puncture is needed to reach one of the
three normalized output domains, with no quadratic coefficient hypothesis.
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
  retainedOlderLowerCoordinates terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k < j)
local notation "hπ" => node.uniformizer_ne_zero
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
variable (hdepth : 2 * j ≤ depth) (hnear : depth ≤ k + 2 * j)
local notation "D" => arithmeticMixedNodalReflectedChart node data m j hj k hk hdepth hnear
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + j)) (e).b3 (e).b4 (e).b6)

/-- All positive unequal punctured inputs reach an actual normalized output domain. -/
theorem arithmeticMixedNodalReflectedChart_punctured (hk0 : 0 < k) (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme)) (hx : x₁ ∉ (input p).asIdeal)
    (hu : x₂ ∉ (input p).asIdeal) : ∃ c, p ∈ D c := by
  have hp := arithmeticRetainedTerminalFormulaInput_parameter_mem
    hπ data m j hj k j hk le_rfl p
  rcases nodalReflectedPuncturedUnequal_cover node d e
    (by change 0 + k ≤ 0 + j; omega) data
    (by change depth - (0 + k) - (0 + j) ≤ n; omega)
    (by change 2 * (0 + j) < depth; omega)
    (by change depth ≤ (0 + k) + 2 * (0 + j); omega) al ar
    (by change 0 < 0 + k; omega) (by change 0 + k < 0 + j; omega)
    (input p) hp hx hu with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

/-- Terminal smoothness supplies the second puncture on the entire original smooth pair. -/
theorem arithmeticMixedNodalReflectedChart_horizontal (hk0 : 0 < k) (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme)) (hx : x₁ ∉ (input p).asIdeal) : ∃ c, p ∈ D c :=
  arithmeticMixedNodalReflectedChart_punctured node data m j hj k hk hdepth hnear hk0 hm p hx
    (arithmeticMixedFormulaInput_nodal_terminal_punctured hπ data m j hj k hk node hm p)

/-- The exact middle endpoint is covered by the genuine difference-depth formula. -/
theorem arithmeticMixedNodalReflectedChart_middle (hm : 2 * j = depth)
    (p : (pullback fa fb : Scheme)) (hx : x₁ ∉ (input p).asIdeal) : p ∈ D 2 := by
  exact unequalDepthDomain_all_middle_mem node d e (Nat.add_le_add_left hk.le 0)
    data (by change (0 + j) - (0 + k) ≤ n; omega) al ar
    (by change 0 + k < 0 + j; omega)
    (by change 2 * (0 + j) = depth; omega) (input p)
    (arithmeticRetainedTerminalFormulaInput_parameter_mem hπ data m j hj k j hk le_rfl p) hx

/-- Positive retained punctures are covered throughout the near-terminal range. -/
theorem arithmeticMixedNodalReflectedChart_near (hk0 : 0 < k)
    (p : (pullback fa fb : Scheme)) (hx : x₁ ∉ (input p).asIdeal) : ∃ c, p ∈ D c := by
  rcases lt_or_eq_of_le hdepth with hm | hm
  · exact arithmeticMixedNodalReflectedChart_horizontal
      node data m j hj k hk hdepth hnear hk0 hm p hx
  · exact ⟨2, arithmeticMixedNodalReflectedChart_middle
      node data m j hj k hk hdepth hnear hm p hx⟩

local notation "next" => data ⟨k + 1, by omega⟩
local notation "I" => (arithmeticRetainedTensorIso hπ data m j hj k hk).inv
local notation "u" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + k)) π
  (next).b3 (next).b4 (next).b6 Q 2

/-- The retained puncture can be tested in its unchanged original tensor coordinates. -/
theorem arithmeticMixedNodalReflectedChart_tensor (hk0 : 0 < k) (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme))
    (hx : u ∉ (I ((O a).ι (pullback.fst fa fb p))).asIdeal) : ∃ c, p ∈ D c :=
  arithmeticMixedNodalReflectedChart_horizontal node data m j hj k hk hdepth hnear hk0 hm p
    (fun hz => hx ((arithmeticMixedFormulaInput_x_iff
      hπ data m j hj k j hk le_rfl p).mp hz))

end FLT.Mazur.WeierstrassDividedDepth
