/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleFactoredSumOutput
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSingleFactoredSumOutput
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSecondFactoredSumOutput
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Actual local outputs for separated retained pairs

The four choices of shifting neither, first, second or both inputs each carry
three genuine formula domains and whole quotient-valued outputs. The sum-depth
bound replaces the older fourfold bound, without imposing quadratic vanishing.
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
  (hiNext : (i + 1) + 2 ≤ k) (hjNext : (j + 1) + 2 ≤ k)
  (hgap : i + 1 < j) (hdepth : 2 * ((i + 2) + (j + 2)) < depth)
  (hsum : (i + 2) + (j + 2) ≤ k)
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
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => tensorCoord W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2

local notation "index" => fun r : ℕ => (Fin.succ ⟨k - r,
  Nat.lt_succ_of_le ((Nat.sub_le k r).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s

local notation "V" => arithmeticTargetFactoredSumOutputChart node data m k hk i j hi hj
  (by omega) (by omega) (by omega)
local notation "SC" => arithmeticRetainedSingleFactoredSumChart node data m k hk
  (i + 1) j hiNext hj (by omega) (by omega) (by omega)
local notation "SO" => arithmeticRetainedSingleFactoredSumOutput node data m k hk
  (i + 1) j hiNext hj (by omega) (by omega) (by omega)
local notation "RC" => arithmeticRetainedSecondFactoredSumChart node data m k hk
  i (j + 1) hi hjNext (by omega) (by omega) (by omega)
local notation "RO" => arithmeticRetainedSecondFactoredSumOutput node data m k hk
  i (j + 1) hi hjNext (by omega) (by omega) (by omega)
local notation "DC" => arithmeticRetainedDoubleFactoredSumChart node data m k hk
  (i + 1) (j + 1) hiNext hjNext (by omega) (by omega) (by omega)
local notation "DO" => arithmeticRetainedDoubleFactoredSumOutput node data m k hk
  (i + 1) (j + 1) hiNext hjNext (by omega) (by omega) (by omega)
local notation "S" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext g
local notation "T" => arithmeticFixedAdjacentPairOpen hπ data m k hk (j + 1) hjNext f
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk
  (i + 1) (j + 1) hiNext hjNext
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Four transfer choices, with three actual formula domains for each. -/
abbrev RetainedSeparatedFactoredSumLocalIndex := (Bool × Bool) × Fin 3

/-- Every local source is an actual open in its original incidence source. -/
def arithmeticRetainedSeparatedFactoredSumLocalSource :
    RetainedSeparatedFactoredSumLocalIndex → Scheme
  | ((false, false), b) => (V b).toScheme
  | ((true, false), b) => (SC b).toScheme
  | ((false, true), b) => (RC b).toScheme
  | ((true, true), b) => (DC b).toScheme

local notation "X" => arithmeticRetainedSeparatedFactoredSumLocalSource
  node data m k hk i j hi hj hiNext hjNext hgap hdepth hsum

/-- Include each genuine formula domain into the original ordered pair. -/
def arithmeticRetainedSeparatedFactoredSumLocalInclusion :
    (b : RetainedSeparatedFactoredSumLocalIndex) → X b ⟶ pullback f g
  | ((false, false), b) => (V b).ι
  | ((true, false), b) => (SC b).ι ≫ (S).ι
  | ((false, true), b) => (RC b).ι ≫ (T).ι ≫ (pullbackSymmetry f g).inv
  | ((true, true), b) => (DC b).ι ≫ (D).ι

local notation "inc" => arithmeticRetainedSeparatedFactoredSumLocalInclusion
  node data m k hk i j hi hj hiNext hjNext hgap hdepth hsum

/-- All twelve sources are open subcharts of the entire original pair. -/
instance arithmeticRetainedSeparatedFactoredSumLocalInclusion_isOpenImmersion
    (b : RetainedSeparatedFactoredSumLocalIndex) : IsOpenImmersion (inc b) := by
  rcases b with ⟨⟨a, b⟩, label⟩
  cases a <;> cases b <;>
    dsimp only [arithmeticRetainedSeparatedFactoredSumLocalInclusion] <;> infer_instance

/-- Every source carries its constructed whole quotient-valued addition output. -/
def arithmeticRetainedSeparatedFactoredSumLocalOutput :
    (b : RetainedSeparatedFactoredSumLocalIndex) → X b ⟶ pullback q t
  | ((false, false), b) => arithmeticTargetFactoredSumQuotientOutput
      node data m k hk i j hi hj (by omega) (by omega) (by omega) b
  | ((true, false), b) => SO b
  | ((false, true), b) => RO b
  | ((true, true), b) => DO b

/-- The complete coefficient morphism is unchanged on every local source. -/
@[reassoc] theorem arithmeticRetainedSeparatedFactoredSumLocalOutput_base
    (b : RetainedSeparatedFactoredSumLocalIndex) :
    arithmeticRetainedSeparatedFactoredSumLocalOutput
      node data m k hk i j hi hj hiNext hjNext hgap hdepth hsum b ≫ pullback.fst q t =
        inc b ≫ pullback.fst f g ≫ f := by
  rcases b with ⟨⟨a, b⟩, label⟩
  cases a <;> cases b <;>
    simp only [arithmeticRetainedSeparatedFactoredSumLocalOutput,
      arithmeticRetainedSeparatedFactoredSumLocalInclusion, Category.assoc,
      arithmeticTargetFactoredSumQuotientOutput_base,
      arithmeticRetainedSingleFactoredSumOutput_base,
      arithmeticRetainedSecondFactoredSumOutput_base,
      arithmeticRetainedDoubleFactoredSumOutput_base]

end FLT.Mazur.WeierstrassDividedDepth
