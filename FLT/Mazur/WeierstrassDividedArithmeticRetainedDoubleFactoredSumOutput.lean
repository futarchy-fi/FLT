/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetFactoredSumQuotientOutput
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticFixedSourceSmooth
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentRange

/-!
# Whole normalized sum-depth outputs after a double retained transfer

Pull the three genuine quotient-valued outputs back to the actual incidence
source. Both original coefficient morphisms are preserved, including nilpotents.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticFixedAdjacentBoundarySource arithmeticFixedAdjacentBoundaryTarget
  arithmeticFixedAdjacentSourceCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (N : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "hπ" => N.uniformizer_ne_zero
local notation "a" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "secondIndex" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj
local notation "t" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj

local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "f" => chart a ≫ s
local notation "g" => chart secondIndex ≫ s
local notation "f'" => chart c ≫ s
local notation "g'" => chart d ≫ s

variable (hij : i ≤ j) (hlo : (i + 1) + 2 * (j + 1) ≤ depth)
  (hsum : (i + 1) + (j + 1) ≤ k)
local notation "K" => t
local notation "inc" => (D).ι
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "V" => arithmeticTargetFactoredSumOutputChart N data m k hk i j hi hj hij hlo hsum
local notation "out" => arithmeticTargetFactoredSumQuotientOutput
  N data m k hk i j hi hj hij hlo hsum
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "st" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The three actual addition domains in the full incidence source. -/
def arithmeticRetainedDoubleFactoredSumChart (b : Fin 3) : (D).toScheme.Opens := K ⁻¹ᵁ V b

local notation "C" => arithmeticRetainedDoubleFactoredSumChart N data m k hk i j hi hj hij hlo hsum

/-- Each source chart carries the full arithmetic quotient output. -/
def arithmeticRetainedDoubleFactoredSumOutput (b : Fin 3) : (C b).toScheme ⟶ pullback q st :=
  (K ∣_ V b) ≫ out b

/-- The output retains the first original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedDoubleFactoredSumOutput_base (b : Fin 3) :
    arithmeticRetainedDoubleFactoredSumOutput N data m k hk i j hi hj hij hlo hsum b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.fst f g ≫ f := by
  rw [arithmeticRetainedDoubleFactoredSumOutput, Category.assoc,
    arithmeticTargetFactoredSumQuotientOutput_base, morphismRestrict_ι_assoc]
  rw [arithmeticRetainedDoubleTransfer_first_assoc]
  rfl

/-- The same output retains the second original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedDoubleFactoredSumOutput_base_snd (b : Fin 3) :
    arithmeticRetainedDoubleFactoredSumOutput N data m k hk i j hi hj hij hlo hsum b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.snd f g ≫ g := by
  rw [arithmeticRetainedDoubleFactoredSumOutput_base, pullback.condition]

/-- Every punctured transfer reaches one of the actual formula charts. -/
theorem arithmeticRetainedDoubleFactoredSumChart_covers
    (hdeep : 2 * ((i + 1) + (j + 1)) < depth) (hlt : i < j) (z : (D).toScheme) :
    ∃ b, z ∈ C b := by
  apply arithmeticTargetFactoredSumOutputChart_punctured N data m k hk i j hi hj hij hlo hsum
    hdeep hlt (K z)
  · exact (arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj z).1
  · exact (arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj z).2

/-- The whole double-transfer incidence source is covered by actual output charts. -/
theorem arithmeticRetainedDoubleFactoredSumChart_top
    (hdeep : 2 * ((i + 1) + (j + 1)) < depth) (hlt : i < j) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨b, hb⟩ := arithmeticRetainedDoubleFactoredSumChart_covers
    N data m k hk i j hi hj hij hlo hsum hdeep hlt z
  exact (le_iSup (fun b => C b) b) hb

/-- An actual open cover of the full double-transfer source, with quotient outputs above. -/
def arithmeticRetainedDoubleFactoredSumCover
    (hdeep : 2 * ((i + 1) + (j + 1)) < depth) (hlt : i < j) :
    (D).toScheme.OpenCover :=
  (D).toScheme.openCoverOfIsOpenCover C
    (arithmeticRetainedDoubleFactoredSumChart_top N data m k hk i j hi hj
      hij hlo hsum hdeep hlt)

end FLT.Mazur.WeierstrassDividedDepth
