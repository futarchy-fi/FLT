/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNodalHorizontalCover

/-!
# Normalized terminal/retained outputs in the reverse input order

Transport the whole normalized domains and outputs through pair symmetry.
The retained puncture is the second input's original coordinate. This does
not assert equality of different addition formulas on their overlaps.
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
local notation "D" => arithmeticMixedNodalReflectedChart node data m j hj k hk hdepth hnear
local notation "H" => arithmeticMixedNodalHorizontalOpen node data m j hj k hk
local notation "swap" => (pullbackSymmetry fb fa).hom

/-- Each normalized domain in the original terminal-first smooth pair. -/
def arithmeticMixedNodalReversedChart (c : Fin 3) : (pullback fb fa).Opens := swap ⁻¹ᵁ D c

local notation "E" => arithmeticMixedNodalReversedChart node data m j hj k hk hdepth hnear

/-- The complete normalized output on each reversed domain. -/
def arithmeticMixedNodalReversedOutput (c : Fin 3) : (E c).toScheme ⟶ pullback q t :=
  (swap ∣_ D c) ≫
    arithmeticMixedNodalReflectedQuotientOutput node data m j hj k hk hdepth hnear c

/-- The reversed output retains the original terminal coefficient morphism. -/
@[reassoc] theorem arithmeticMixedNodalReversedOutput_base (c : Fin 3) :
    arithmeticMixedNodalReversedOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (E c).ι ≫ pullback.fst fb fa ≫ fb := by
  rw [arithmeticMixedNodalReversedOutput, Category.assoc,
    arithmeticMixedNodalReflectedQuotientOutput_base, morphismRestrict_ι_assoc,
    pullbackSymmetry_hom_comp_fst_assoc, ← pullback.condition]
  rfl

/-- The unchanged retained puncture in the second input. -/
def arithmeticMixedNodalReversedHorizontalOpen : (pullback fb fa).Opens := swap ⁻¹ᵁ H

local notation "J" => arithmeticMixedNodalReversedHorizontalOpen node data m j hj k hk

/-- Each actual formula chart restricted to the reversed retained puncture. -/
def arithmeticMixedNodalReversedHorizontalChart (c : Fin 3) : (J).toScheme.Opens :=
  (J).ι ⁻¹ᵁ E c

local notation "C" => arithmeticMixedNodalReversedHorizontalChart
  node data m j hj k hk hdepth hnear

/-- The restricted chart still has the entire quotient output. -/
def arithmeticMixedNodalReversedHorizontalOutput (c : Fin 3) : (C c).toScheme ⟶ pullback q t :=
  ((J).ι ∣_ E c) ≫ arithmeticMixedNodalReversedOutput node data m j hj k hk hdepth hnear c

/-- No quotient coefficients are lost by reversing or restricting the pair. -/
@[reassoc] theorem arithmeticMixedNodalReversedHorizontalOutput_base (c : Fin 3) :
    arithmeticMixedNodalReversedHorizontalOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (C c).ι ≫ (J).ι ≫ pullback.fst fb fa ≫ fb := by
  rw [arithmeticMixedNodalReversedHorizontalOutput, Category.assoc,
    arithmeticMixedNodalReversedOutput_base, morphismRestrict_ι_assoc]
  rfl

/-- The three reversed domains cover every point of the original retained puncture. -/
theorem arithmeticMixedNodalReversedHorizontalChart_covers (hk0 : 0 < k) :
    (⨆ c, C c) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨c, hc⟩ := arithmeticMixedNodalReflectedChart_near
    node data m j hj k hk hdepth hnear hk0 (swap p.val) p.property
  exact (le_iSup (fun c => C c) c) hc

/-- An actual normalized open cover in the reverse original input order. -/
def arithmeticMixedNodalReversedHorizontalCover (hk0 : 0 < k) : (J).toScheme.OpenCover :=
  (J).toScheme.openCoverOfIsOpenCover C
    (arithmeticMixedNodalReversedHorizontalChart_covers node data m j hj k hk hdepth hnear hk0)

end FLT.Mazur.WeierstrassDividedDepth
