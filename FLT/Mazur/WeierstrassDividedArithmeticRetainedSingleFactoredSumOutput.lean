/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetFactoredSumQuotientOutput
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage

/-!
# Whole normalized sum-depth outputs after a single retained transfer

Pull the three genuine quotient-valued outputs back to the actual incidence
source. Both original coefficient morphisms are preserved, including nilpotents.
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
  (hij : i ≤ j) (hlo : (i + 1) + 2 * (j + 1) ≤ depth)
  (hsum : (i + 1) + (j + 1) ≤ k)
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
local notation "dj" => data ⟨j + 1, by omega⟩
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "O₊" => arithmeticTargetFactoredSumPositiveOpen node data m k hk i j hi hj
  hij hlo hsum
local notation "O₋" => arithmeticTargetFactoredSumNegativeOpen node data m k hk i j hi hj
  hij hlo hsum
local notation "O₀" => arithmeticTargetFactoredSumOppositeOpen node data m k hk i j hi hj hij hsum
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "oldIndex" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "oldCoords" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk i hi
local notation "oldU" => tensorCoord W (π ^ (0 + i)) π
  (Data.b3 di) (Data.b4 di) (Data.b6 di) Q 2
local notation "f" => chart oldIndex ≫ s
local notation "f'" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "D" => arithmeticFixedAdjacentPairOpen hπ data m k hk i hi g
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk i hi g

local notation "K" => T
local notation "inc" => (D).ι

local notation "V" => arithmeticTargetFactoredSumOutputChart node data m k hk i j hi hj hij hlo hsum
local notation "out" => arithmeticTargetFactoredSumQuotientOutput
  node data m k hk i j hi hj hij hlo hsum
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "st" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The three actual addition domains in the full incidence source. -/
def arithmeticRetainedSingleFactoredSumChart (b : Fin 3) : (D).toScheme.Opens := K ⁻¹ᵁ V b

local notation "C" => arithmeticRetainedSingleFactoredSumChart
  node data m k hk i j hi hj hij hlo hsum

/-- Each source chart carries the full arithmetic quotient output. -/
def arithmeticRetainedSingleFactoredSumOutput (b : Fin 3) : (C b).toScheme ⟶ pullback q st :=
  (K ∣_ V b) ≫ out b

/-- The output retains the first original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedSingleFactoredSumOutput_base (b : Fin 3) :
    arithmeticRetainedSingleFactoredSumOutput node data m k hk i j hi hj hij hlo hsum b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.fst f g ≫ f := by
  rw [arithmeticRetainedSingleFactoredSumOutput, Category.assoc,
    arithmeticTargetFactoredSumQuotientOutput_base, morphismRestrict_ι_assoc]
  rw [arithmeticFixedAdjacentPairTransfer_first_assoc]
  rfl

/-- The same output retains the second original coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedSingleFactoredSumOutput_base_snd (b : Fin 3) :
    arithmeticRetainedSingleFactoredSumOutput node data m k hk i j hi hj hij hlo hsum b ≫
      pullback.fst q st = (C b).ι ≫ inc ≫ pullback.snd f g ≫ g := by
  rw [arithmeticRetainedSingleFactoredSumOutput_base, pullback.condition]

/-- Every punctured transfer reaches one of the actual formula charts. -/
theorem arithmeticRetainedSingleFactoredSumChart_covers
    (hdeep : 2 * ((i + 1) + (j + 1)) < depth) (hlt : i < j) (z : (D).toScheme)
    (hv : v ∉ (J (pullback.snd f g ((D).ι z))).asIdeal) : ∃ b, z ∈ C b := by
  apply arithmeticTargetFactoredSumOutputChart_punctured node data m k hk i j hi hj hij hlo hsum
    hdeep hlt (K z)
  · exact arithmeticFixedAdjacentPairTransfer_punctured hπ data m k hk i hi g z
  · have he := congrArg (fun morphism => morphism z)
      (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk i hi g)
    change pullback.snd f' g (T z) = pullback.snd f g ((D).ι z) at he
    rw [he]
    exact hv

end FLT.Mazur.WeierstrassDividedDepth
