/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalMixedNodalOutput

/-!
# Covering terminal transfer sources with normalized mixed outputs

The retained puncture is measured in the original second input. On this
open of the full smooth incidence source, all normalized domains cover and
carry their actual quotient outputs at the unchanged final stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (k : ℕ) (hk : k < j + 1)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => (Fin.succ ⟨j + 1 - j, by omega⟩ : Fin (j + 1 + 3))
local notation "b" => retainedOlderFormulaIndex (j + 1) k hk
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj
local notation "fa" => (O 1).ι ≫ chart 1 ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "B" => arithmeticTerminalPairOpen hπ data m j hj (chart b ≫ s)
local notation "x" => arithmeticTerminalAtlasSourceFirst hπ data m j hj b
local notation "y" => arithmeticTerminalAtlasSourceSecond hπ data m j hj b
local notation "z" => arithmeticTerminalAtlasTargetFirst hπ data m j hj b
local notation "w" => arithmeticTerminalAtlasTargetSecond hπ data m j hj b
local notation "h₁" => arithmeticTerminalAtlasInputs_first hπ data m j hj b
local notation "h₂" => congrArg (fun f => f ≫ chart b)
  (arithmeticTerminalAtlasInputs_second hπ data m j hj b)
local notation "hb" => arithmeticTerminalAtlasInputs_base hπ data m j hj b
local notation "D" => arithmeticTerminalAtlasSmoothOpen hπ data m j hj b

local notation "T" => arithmeticTerminalMixedNodalTarget node data m j hj k hk
local notation "H" => arithmeticMixedNodalReversedHorizontalOpen node data m (j + 1) hj k hk

/-- The retained-punctured open of the genuine smooth terminal incidence source. -/
def arithmeticTerminalMixedNodalHorizontalOpen : (D).toScheme.Opens := T ⁻¹ᵁ H

local notation "A" => arithmeticTerminalMixedNodalHorizontalOpen node data m j hj k hk
local notation "next" => data ⟨k + 1, by omega⟩
local notation "I" => (arithmeticRetainedTensorIso hπ data m (j + 1) hj k hk).inv
local notation "u" => WeierstrassSuccessiveX.tensorCoord W (π ^ (0 + k)) π
  (next).b3 (next).b4 (next).b6 Q 2
local notation "swap" => (pullbackSymmetry fa fb).hom
local notation "input" => arithmeticRetainedTerminalFormulaInput
  hπ data m (j + 1) hj k (j + 1) hk le_rfl
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "x₁" => unequalPairLeft d e
  (WeierstrassDilatation.x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)

/-- The domain tests only the unchanged second retained input's original tensor coordinate. -/
theorem arithmeticTerminalMixedNodalHorizontalOpen_mem (p : (D).toScheme) :
    p ∈ A ↔ u ∉ (I (y ((D).ι p))).asIdeal := by
  change x₁ ∉ (input (swap (T p))).asIdeal ↔ _
  rw [arithmeticMixedFormulaInput_x_iff, SchemePairSymmetryPoints.fst_apply]
  have he := congrArg (fun f => f p)
    (arithmeticTerminalMixedNodalTarget_second node data m j hj k hk)
  change (O b).ι (pullback.snd fa fb (T p)) = y ((D).ι p) at he
  rw [he]

variable (hdepth : 2 * (j + 1) ≤ depth) (hnear : depth ≤ k + 2 * (j + 1))
local notation "C" => arithmeticTerminalMixedNodalChart node data m j hj k hk hdepth hnear

/-- Restrict every actual terminal-boundary formula to the retained puncture. -/
def arithmeticTerminalMixedNodalHorizontalChart (c : Fin 3) : (A).toScheme.Opens :=
  (A).ι ⁻¹ᵁ C c

local notation "V" => arithmeticTerminalMixedNodalHorizontalChart
  node data m j hj k hk hdepth hnear

/-- Every restricted terminal-boundary chart retains its actual quotient output. -/
def arithmeticTerminalMixedNodalHorizontalOutput (c : Fin 3) :
    (V c).toScheme ⟶ pullback q t :=
  ((A).ι ∣_ C c) ≫ arithmeticTerminalMixedNodalOutput node data m j hj k hk hdepth hnear c

/-- The original first coefficient map is preserved through both genuine restrictions. -/
@[reassoc] theorem arithmeticTerminalMixedNodalHorizontalOutput_base (c : Fin 3) :
    arithmeticTerminalMixedNodalHorizontalOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (V c).ι ≫ (A).ι ≫ (D).ι ≫ (B).ι ≫
        pullback.fst (old ≫ s) (chart b ≫ s) ≫ old ≫ s := by
  rw [arithmeticTerminalMixedNodalHorizontalOutput, Category.assoc,
    arithmeticTerminalMixedNodalOutput_base, morphismRestrict_ι_assoc]
  rfl

/-- Every point of the retained-punctured terminal boundary reaches a normalized output. -/
theorem arithmeticTerminalMixedNodalHorizontalChart_covers (hk0 : 0 < k) :
    (⨆ c, V c) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨c, hc⟩ := arithmeticMixedNodalReflectedChart_near
    node data m (j + 1) hj k hk hdepth hnear hk0 (swap (T p.val)) p.property
  exact (le_iSup (fun c => V c) c) hc

/-- A genuine open cover of this terminal-transfer boundary, with all outputs above. -/
def arithmeticTerminalMixedNodalHorizontalCover (hk0 : 0 < k) : (A).toScheme.OpenCover :=
  (A).toScheme.openCoverOfIsOpenCover V
    (arithmeticTerminalMixedNodalHorizontalChart_covers
      node data m j hj k hk hdepth hnear hk0)

end FLT.Mazur.WeierstrassDividedDepth
