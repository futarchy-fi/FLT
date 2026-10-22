/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedNodalReflectedCoverage

/-!
# An actual normalized cover of the retained-punctured mixed pair

Restrict the three genuine formula domains to the retained horizontal open.
Their union is the entire open, and every chart retains its full quotient
output. No terminal puncture or quadratic coefficient premise is imposed.
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
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)

/-- Only the retained factor is punctured inside the full original smooth pair. -/
def arithmeticMixedNodalHorizontalOpen : (pullback fa fb).Opens :=
  input ⁻¹ᵁ PrimeSpectrum.basicOpen x₁

local notation "H" => arithmeticMixedNodalHorizontalOpen node data m j hj k hk

/-- Restrict each actual normalized formula domain to the retained puncture. -/
def arithmeticMixedNodalHorizontalChart (c : Fin 3) : (H).toScheme.Opens := (H).ι ⁻¹ᵁ D c

local notation "C" => arithmeticMixedNodalHorizontalChart node data m j hj k hk hdepth hnear

/-- Every chart has its whole constructed quotient output. -/
def arithmeticMixedNodalHorizontalOutput (c : Fin 3) : (C c).toScheme ⟶ pullback q t :=
  ((H).ι ∣_ D c) ≫
    arithmeticMixedNodalReflectedQuotientOutput node data m j hj k hk hdepth hnear c

/-- Restriction preserves the complete original coefficient morphism. -/
@[reassoc] theorem arithmeticMixedNodalHorizontalOutput_base (c : Fin 3) :
    arithmeticMixedNodalHorizontalOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (C c).ι ≫ (H).ι ≫ pullback.fst fa fb ≫ fa := by
  rw [arithmeticMixedNodalHorizontalOutput, Category.assoc,
    arithmeticMixedNodalReflectedQuotientOutput_base, morphismRestrict_ι_assoc]
  rfl

/-- All three genuine domains together cover the entire retained-punctured smooth pair. -/
theorem arithmeticMixedNodalHorizontalChart_covers (hk0 : 0 < k) :
    (⨆ c, C c) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨c, hc⟩ := arithmeticMixedNodalReflectedChart_near
    node data m j hj k hk hdepth hnear hk0 p.val p.property
  exact (le_iSup (fun c => C c) c) hc

/-- An open cover carrying normalized quotient-valued outputs at every arithmetic order. -/
def arithmeticMixedNodalHorizontalCover (hk0 : 0 < k) :
    (H).toScheme.OpenCover :=
  (H).toScheme.openCoverOfIsOpenCover C
    (arithmeticMixedNodalHorizontalChart_covers node data m j hj k hk hdepth hnear hk0)

end FLT.Mazur.WeierstrassDividedDepth
