/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetFlexiblePreMiddle
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticFixedSourceSmooth
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentRange

/-!
# Flexible outputs after a double retained transfer

Pull the stage-efficient unequal target formulas back to the actual incidence
source. Both original coefficient morphisms, including nilpotents, are retained.
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

variable (hij : i ≤ j) (hpre : 2 * (j + 1) < depth)
  (hstage : min ((i + 1) + (j + 1)) (depth - (i + 1) - (j + 1)) ≤ k)
local notation "K" => t
local notation "inc" => (D).ι
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "V" => arithmeticTargetFlexiblePreMiddleChart N data m k hk i j hi hj hij hpre hstage
local notation "out" => arithmeticTargetFlexiblePreMiddleOutput
  N data m k hk i j hi hj hij hpre hstage
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "st" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The three actual addition domains in the full incidence source. -/
def arithmeticRetainedDoubleFlexiblePreMiddleChart (b : Fin 3) : (D).toScheme.Opens := K ⁻¹ᵁ V b

local notation "C" => arithmeticRetainedDoubleFlexiblePreMiddleChart
  N data m k hk i j hi hj hij hpre hstage

/-- Each source chart carries the full arithmetic quotient output. -/
def arithmeticRetainedDoubleFlexiblePreMiddleOutput (b : Fin 3) : (C b).toScheme ⟶ pullback q st :=
  (K ∣_ V b) ≫ out b

/-- The output retains the first original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedDoubleFlexiblePreMiddleOutput_base (b : Fin 3) :
    arithmeticRetainedDoubleFlexiblePreMiddleOutput N data m k hk i j hi hj hij hpre hstage b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.fst f g ≫ f := by
  rw [arithmeticRetainedDoubleFlexiblePreMiddleOutput, Category.assoc,
    arithmeticTargetFlexiblePreMiddleOutput_base, morphismRestrict_ι_assoc]
  rw [arithmeticRetainedDoubleTransfer_first_assoc]
  rfl

/-- The same output retains the second original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedDoubleFlexiblePreMiddleOutput_base_snd (b : Fin 3) :
    arithmeticRetainedDoubleFlexiblePreMiddleOutput N data m k hk i j hi hj hij hpre hstage b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.snd f g ≫ g := by
  rw [arithmeticRetainedDoubleFlexiblePreMiddleOutput_base, pullback.condition]

/-- Every punctured transfer reaches one of the actual formula charts. -/
theorem arithmeticRetainedDoubleFlexiblePreMiddleChart_covers
    (hlt : i < j) (z : (D).toScheme) :
    ∃ b, z ∈ C b := by
  apply arithmeticTargetFlexiblePreMiddleChart_punctured N data m k hk i j hi hj hij hpre hstage
    hlt (K z)
  · exact (arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj z).1
  · exact (arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj z).2

/-- The whole double-transfer incidence source is covered by actual output charts. -/
theorem arithmeticRetainedDoubleFlexiblePreMiddleChart_top
    (hlt : i < j) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨b, hb⟩ := arithmeticRetainedDoubleFlexiblePreMiddleChart_covers
    N data m k hk i j hi hj hij hpre hstage hlt z
  exact (le_iSup (fun b => C b) b) hb

/-- An actual open cover of the full double-transfer source, with quotient outputs above. -/
def arithmeticRetainedDoubleFlexiblePreMiddleCover
    (hlt : i < j) :
    (D).toScheme.OpenCover :=
  (D).toScheme.openCoverOfIsOpenCover C
    (arithmeticRetainedDoubleFlexiblePreMiddleChart_top N data m k hk i j hi hj
      hij hpre hstage hlt)

end FLT.Mazur.WeierstrassDividedDepth
