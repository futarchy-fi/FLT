/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetFlexiblePreMiddle
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage
public import FLT.Mazur.SchemePairSymmetryPoints

/-!
# Flexible outputs after a second retained transfer

Pull the stage-efficient unequal target formulas back to the actual incidence
source. Both original coefficient morphisms, including nilpotents, are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
  (hij : i ≤ j) (hpre : 2 * (j + 1) < depth)
  (hstage : min ((i + 1) + (j + 1)) (depth - (i + 1) - (j + 1)) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨j + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "oldIndex" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "oldCoords" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "oldU" => tensorCoord W (π ^ (0 + j)) π
  (Data.b3 dj) (Data.b4 dj) (Data.b6 dj) Q 2
local notation "f" => chart c ≫ s
local notation "g" => chart oldIndex ≫ s
local notation "g'" => chart d ≫ s
local notation "swap" => (pullbackSymmetry f g).hom
local notation "back" => (pullbackSymmetry g' f).hom

local notation "D" => arithmeticFixedAdjacentPairOpen hπ data m k hk j hj f
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk j hj f
local notation "K" => T ≫ back
local notation "inc" => (D).ι ≫ (pullbackSymmetry f g).inv

local notation "V" => arithmeticTargetFlexiblePreMiddleChart
  node data m k hk i j hi hj hij hpre hstage
local notation "out" => arithmeticTargetFlexiblePreMiddleOutput
  node data m k hk i j hi hj hij hpre hstage
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "st" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The three actual addition domains in the full incidence source. -/
def arithmeticRetainedSecondFlexiblePreMiddleChart (b : Fin 3) : (D).toScheme.Opens := K ⁻¹ᵁ V b

local notation "C" => arithmeticRetainedSecondFlexiblePreMiddleChart
  node data m k hk i j hi hj hij hpre hstage

/-- Each source chart carries the full arithmetic quotient output. -/
def arithmeticRetainedSecondFlexiblePreMiddleOutput (b : Fin 3) : (C b).toScheme ⟶ pullback q st :=
  (K ∣_ V b) ≫ out b

/-- The output retains the first original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedSecondFlexiblePreMiddleOutput_base (b : Fin 3) :
    arithmeticRetainedSecondFlexiblePreMiddleOutput node data m k hk i j hi hj hij hpre hstage b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.fst f g ≫ f := by
  rw [arithmeticRetainedSecondFlexiblePreMiddleOutput, Category.assoc,
    arithmeticTargetFlexiblePreMiddleOutput_base, morphismRestrict_ι_assoc]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackSymmetry_inv_comp_fst_assoc]
  rw [arithmeticFixedAdjacentPairTransfer_second_assoc]
  rfl

/-- The same output retains the second original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedSecondFlexiblePreMiddleOutput_base_snd (b : Fin 3) :
    arithmeticRetainedSecondFlexiblePreMiddleOutput node data m k hk i j hi hj hij hpre hstage b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.snd f g ≫ g := by
  rw [arithmeticRetainedSecondFlexiblePreMiddleOutput_base, pullback.condition]

/-- Every punctured transfer reaches one of the actual formula charts. -/
theorem arithmeticRetainedSecondFlexiblePreMiddleChart_covers
    (hlt : i < j) (z : (D).toScheme)
    (hu : u ∉ (I (pullback.snd g f ((D).ι z))).asIdeal) : ∃ b, z ∈ C b := by
  apply arithmeticTargetFlexiblePreMiddleChart_punctured node data m k hk i j hi hj hij hpre hstage
    hlt (K z)
  · change u ∉ (I (pullback.fst f g' (back (T z)))).asIdeal
    rw [SchemePairSymmetryPoints.fst_apply]
    have he := congrArg (fun morphism => morphism z)
      (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk j hj f)
    change pullback.snd g' f (T z) = pullback.snd g f ((D).ι z) at he
    rw [he]
    exact hu
  · have hv := arithmeticFixedAdjacentPairTransfer_punctured hπ data m k hk j hj f z
    simpa only [Scheme.Hom.comp_apply, SchemePairSymmetryPoints.snd_apply] using hv

end FLT.Mazur.WeierstrassDividedDepth
