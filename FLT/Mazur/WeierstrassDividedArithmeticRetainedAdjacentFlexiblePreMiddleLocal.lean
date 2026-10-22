/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleFlexiblePreMiddleOutput
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentSelfFlexibleTransfer
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSecondFlexiblePreMiddleOutput
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Flexible adjacent retained-pair local

Cover the full smooth pair through actual unshifted and transferred domains.
Each target chooses its sum-depth or reflected formula, with the output stage
bounded by the maximum of the three actual smaller sum/reflected depths.
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
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
  (hiNext : (i + 1) + 2 ≤ k) (hiLast : ((i + 1) + 1) + 2 ≤ k)
  (hpre : 2 * ((i + 1) + 2) < depth)
  (hstage : max (min (2 * i + 3) (depth - (2 * i + 3)))
    (max (min (2 * i + 4) (depth - (2 * i + 4)))
      (min (2 * i + 5) (depth - (2 * i + 5)))) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨(i + 1) + 2, Nat.lt_succ_of_le (hiNext.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - ((i + 1) + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k ((i + 1) + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk (i + 1) hiNext

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨(i + 1) + 1, by omega⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + ((i + 1) + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "V" => arithmeticTargetFlexiblePreMiddleChart node data m k hk i (i + 1) hi hiNext
  (by omega) (by omega) (by omega)
local notation "SC" => arithmeticRetainedAdjacentSelfFlexibleTransferChart node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "SO" => arithmeticRetainedAdjacentSelfFlexibleTransferOutput node data m k hk
  (i + 1) hiNext (by omega) (by omega)
local notation "RC" => arithmeticRetainedSecondFlexiblePreMiddleChart node data m k hk
  i ((i + 1) + 1) hi hiLast (by omega) (by omega) (by omega)
local notation "RO" => arithmeticRetainedSecondFlexiblePreMiddleOutput node data m k hk
  i ((i + 1) + 1) hi hiLast (by omega) (by omega) (by omega)
local notation "DC" => arithmeticRetainedDoubleFlexiblePreMiddleChart node data m k hk
  (i + 1) ((i + 1) + 1) hiNext hiLast (by omega) (by omega) (by omega)
local notation "DO" => arithmeticRetainedDoubleFlexiblePreMiddleOutput node data m k hk
  (i + 1) ((i + 1) + 1) hiNext hiLast (by omega) (by omega) (by omega)
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext g
local notation "T" => arithmeticFixedAdjacentPairOpen hπ data m k hk ((i + 1) + 1) hiLast f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk
  (i + 1) ((i + 1) + 1) hiNext hiLast
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Three unequal-depth formulas and two equal-depth formulas, in transfer order. -/
abbrev RetainedAdjacentFlexiblePreMiddleLocalIndex := Fin 3 ⊕ (Bool ⊕ (Fin 3 ⊕ Fin 3))

/-- Every local source is an actual open in its original incidence source. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleLocalSource :
    RetainedAdjacentFlexiblePreMiddleLocalIndex → Scheme
  | .inl b => (V b).toScheme
  | .inr (.inl b) => (SC b).toScheme
  | .inr (.inr (.inl b)) => (RC b).toScheme
  | .inr (.inr (.inr b)) => (DC b).toScheme

local notation "X" => arithmeticRetainedAdjacentFlexiblePreMiddleLocalSource
  node data m k hk i hi hiNext hiLast hpre hstage

/-- Include each genuine formula domain into the original ordered pair. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleLocalInclusion :
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) → X b ⟶ pullback f g
  | .inl b => (V b).ι
  | .inr (.inl b) => (SC b).ι ≫ (S).ι
  | .inr (.inr (.inl b)) => (RC b).ι ≫ (T).ι ≫ (pullbackSymmetry f g).inv
  | .inr (.inr (.inr b)) => (DC b).ι ≫ (D).ι

local notation "inc" => arithmeticRetainedAdjacentFlexiblePreMiddleLocalInclusion
  node data m k hk i hi hiNext hiLast hpre hstage

/-- All eleven sources are open subcharts of the entire original pair. -/
instance arithmeticRetainedAdjacentFlexiblePreMiddleLocalInclusion_isOpenImmersion
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) : IsOpenImmersion (inc b) := by
  rcases b with b | (b | (b | b)) <;>
    dsimp only [arithmeticRetainedAdjacentFlexiblePreMiddleLocalInclusion] <;> infer_instance

/-- Every source carries its constructed whole quotient-valued addition output. -/
def arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput :
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) → X b ⟶ pullback q t
  | .inl b => arithmeticTargetFlexiblePreMiddleOutput
      node data m k hk i (i + 1) hi hiNext (by omega) (by omega) (by omega) b
  | .inr (.inl b) => SO b
  | .inr (.inr (.inl b)) => RO b
  | .inr (.inr (.inr b)) => DO b

/-- The complete coefficient morphism is unchanged on every local source. -/
@[reassoc] theorem arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput_base
    (b : RetainedAdjacentFlexiblePreMiddleLocalIndex) :
    arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput
      node data m k hk i hi hiNext hiLast hpre hstage b ≫ pullback.fst q t =
        inc b ≫ pullback.fst f g ≫ f := by
  rcases b with b | (b | (b | b)) <;>
    simp only [arithmeticRetainedAdjacentFlexiblePreMiddleLocalOutput,
      arithmeticRetainedAdjacentFlexiblePreMiddleLocalInclusion, Category.assoc,
      arithmeticTargetFlexiblePreMiddleOutput_base,
      arithmeticRetainedAdjacentSelfFlexibleTransferOutput_base,
      arithmeticRetainedSecondFlexiblePreMiddleOutput_base,
      arithmeticRetainedDoubleFlexiblePreMiddleOutput_base]

end FLT.Mazur.WeierstrassDividedDepth
