/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedZeroNodalCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalReflectedPositive
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalReflectedNegative
public import FLT.Mazur.WeierstrassDividedPreMiddleBranchDichotomy

/-!
# All punctured positive retained branches near the terminal depth

The two reflected output domains and the difference-depth output cover every
branch choice. Terminal puncturing follows from relative smoothness. The
retained puncture is tested in its original arithmetic tensor algebra.
The reflected formulas retain their explicit vanishing hypothesis on a₂.
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
local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (WeierstrassDilatation.x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (WeierstrassDilatation.y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₂" => ar (WeierstrassDilatation.y W (π ^ (0 + j)) (e).b3 (e).b4 (e).b6)
local notation "α" => algebraMap R (UnequalPairRing d e) W.a₁
local notation "C₁" => WeierstrassDilatation.dividedTangentBranchFactor
  W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 al
local notation "C₂" => WeierstrassDilatation.dividedTangentBranchFactor
  W (π ^ (0 + j)) (e).b3 (e).b4 (e).b6 ar

/-- Actual smooth-output domains cover every punctured positive retained branch near terminal. -/
theorem arithmeticMixed_near_terminal_cover (hk0 : 0 < k) (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme))
    (hx : u ∉ (I ((O a).ι (pullback.fst fa fb p))).asIdeal) :
    p ∈ Dpos ∨ p ∈ Dneg ∨ p ∈ D := by
  have hp := arithmeticRetainedTerminalFormulaInput_parameter_mem
    hπ data m j hj k j hk le_rfl p
  have hx₁ : x₁ ∉ (input p).asIdeal := fun hz => hx
    ((arithmeticMixedFormulaInput_x_iff hπ data m j hj k j hk le_rfl p).mp hz)
  have hx₂ := arithmeticMixedFormulaInput_nodal_terminal_punctured
    hπ data m j hj k hk node hm p
  have hkm : 2 * (0 + k) < depth := by omega
  have hjm : 2 * (0 + j) < depth := by omega
  have hb₁ := preMiddleInput_branch_dichotomy node d al
    (by change 0 < 0 + k; omega) hkm (input p) hp
  have hb₂ := preMiddleInput_branch_dichotomy node e ar
    (by change 0 < 0 + j; omega) hjm (input p) hp
  have h3₁ := preMiddleInput_b3_mem node d hkm (input p) hp
  have h3₂ := preMiddleInput_b3_mem node e hjm (input p) hp
  have neg₁ (h : C₁ ∈ (input p).asIdeal) : y₁ + α * x₁ ∈ (input p).asIdeal := by
    simpa only [WeierstrassDilatation.dividedTangentBranchFactor, add_sub_cancel_right]
      using (input p).asIdeal.sub_mem h h3₁
  have neg₂ (h : C₂ ∈ (input p).asIdeal) : y₂ + α * x₂ ∈ (input p).asIdeal := by
    simpa only [WeierstrassDilatation.dividedTangentBranchFactor, add_sub_cancel_right]
      using (input p).asIdeal.sub_mem h h3₂
  rcases hb₁ with hy | hy <;> rcases hb₂ with hv | hv
  · exact Or.inl (arithTerminalReflectedPositiveOpen_mem node data m j hj k j hk le_rfl
      hk.le hdepth hnear hsum h2 hk0 hk hm p hx₁ hx₂ hy hv)
  · exact Or.inr (Or.inr (arithmeticMixed_opposite_mem hπ data m j hj k j hk le_rfl hk.le
      node hk0 hk hm p hx₁ hx₂ (Or.inl ⟨hy, neg₂ hv⟩)))
  · exact Or.inr (Or.inr (arithmeticMixed_opposite_mem hπ data m j hj k j hk le_rfl hk.le
      node hk0 hk hm p hx₁ hx₂ (Or.inr ⟨neg₁ hy, hv⟩)))
  · exact Or.inr (Or.inl (arithTerminalReflectedNegativeOpen_mem node data m j hj k j hk
      le_rfl hk.le hdepth hnear hsum h2 hk0 hk hm p hx₁ hx₂ hy hv))

end FLT.Mazur.WeierstrassDividedDepth
