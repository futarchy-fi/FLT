/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedCoverage
public import FLT.Mazur.WeierstrassDividedNodalReflectedPuncturedCover

/-!
# Normalized reflected outputs for retained/terminal arithmetic pairs

Use the constructed finite normalization on the full mixed input spectrum.
No vanishing quadratic coefficient is required. The terminal input keeps its
final depth and each of the three domains carries a whole quotient output.
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
local notation "hs" => (by omega : depth - (0 + k) - (0 + j) ≤ j)
local notation "hn" => (by omega : depth - (0 + k) - (0 + j) ≤ n)
local notation "hl" => (by omega : 2 * (0 + j) ≤ depth)
local notation "hm" => (by omega : depth ≤ (0 + k) + 2 * (0 + j))
local notation "hkl" => (by omega : 0 + k ≤ 0 + j)
local notation "V₊" => nodalReflectedDomain node d e hkl data hn hl hm al ar
local notation "V₋" => nodalReflectedNegativeDomain node d e hkl data hn hl hm al ar
local notation "V₀" => unequalDepthDomain hπ d e hkl data (by omega) al ar

/-- The actual normalized positive, negative and opposite domains on the full mixed pair. -/
def arithmeticMixedNodalReflectedChart : Fin 3 → (pullback fa fb).Opens
  | 0 => input ⁻¹ᵁ V₊
  | 1 => input ⁻¹ᵁ V₋
  | 2 => input ⁻¹ᵁ V₀

local notation "D" => arithmeticMixedNodalReflectedChart node data m j hj k hk hdepth hnear

/-- Each domain has the entire normalized smooth output. -/
def arithmeticMixedNodalReflectedOutput : (c : Fin 3) → (D c).toScheme ⟶ (U).toScheme
  | 0 => (input ∣_ V₊) ≫
      nodalReflectedResolvedAddition node d e hkl data hn hl hm al ar j hj hs
  | 1 => (input ∣_ V₋) ≫
      nodalReflectedNegativeAddition node d e hkl data hn hl hm al ar j hj hs
  | 2 => (input ∣_ V₀) ≫
      unequalDepthResolvedAddition hπ d e hkl data (by omega) al ar j hj
        (by change (0 + j) - (0 + k) ≤ j; omega)

local notation "out" => arithmeticMixedNodalReflectedOutput node data m j hj k hk hdepth hnear

/-- Normalization preserves the original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticMixedNodalReflectedOutput_structure (c : Fin 3) :
    out c ≫ t = (D c).ι ≫ pullback.fst fa fb ≫ fa ≫ q := by
  fin_cases c <;>
    simp only [arithmeticMixedNodalReflectedOutput, Category.assoc,
      nodalReflectedResolvedAddition_structure, nodalReflectedNegativeAddition_structure,
      unequalDepthResolvedAddition_structure, morphismRestrict_ι_assoc,
      arithmeticRetainedTerminalFormulaInput_structure] <;> rfl

/-- Lift the actual smooth output over the original, possibly nonreduced quotient. -/
def arithmeticMixedNodalReflectedQuotientOutput (c : Fin 3) : (D c).toScheme ⟶ pullback q t :=
  pullback.lift ((D c).ι ≫ pullback.fst fa fb ≫ fa) (out c) (by
    simpa only [Category.assoc] using
      (arithmeticMixedNodalReflectedOutput_structure node data m j hj k hk hdepth hnear c).symm)

/-- The quotient projection retains all original coefficients. -/
@[reassoc] theorem arithmeticMixedNodalReflectedQuotientOutput_base (c : Fin 3) :
    arithmeticMixedNodalReflectedQuotientOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (D c).ι ≫ pullback.fst fa fb ≫ fa := by
  simp only [arithmeticMixedNodalReflectedQuotientOutput, pullback.lift_fst]

/-- The integral projection recovers the entire constructed smooth output. -/
@[reassoc] theorem arithmeticMixedNodalReflectedQuotientOutput_integral (c : Fin 3) :
    arithmeticMixedNodalReflectedQuotientOutput node data m j hj k hk hdepth hnear c ≫
      pullback.snd q t = out c := by
  simp only [arithmeticMixedNodalReflectedQuotientOutput, pullback.lift_snd]

end FLT.Mazur.WeierstrassDividedDepth
