/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetFactoredSumQuotientOutput
public import FLT.Mazur.WeierstrassDividedArithmeticTargetWiderBoundaryQuotientOutput
public import FLT.Mazur.WeierstrassDividedArithmeticTargetReflectedQuotientOutput

/-!
# Flexible unequal targets before the middle depth

Select the actual sum-depth, wider-boundary or reflected formulas according to
node depth. The final stage only needs the smaller of the sum depth and its
reflection, while every selected output retains the whole quotient morphism.
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
local notation "A" => ScalarExtension W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "B" => ScalarExtension W (π ^ (0 + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus

local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Select genuine domains and their outputs together, so their source types agree. -/
def arithmeticTargetFlexiblePreMiddleData (b : Fin 3) :
    Σ O : (pullback f g).Opens, O.toScheme ⟶ pullback q t :=
  if _hs : 2 * ((i + 1) + (j + 1)) < depth then
    ⟨arithmeticTargetFactoredSumOutputChart node data m k hk i j hi hj
        hij (by omega) (by omega) b,
      arithmeticTargetFactoredSumQuotientOutput node data m k hk i j hi hj
        hij (by omega) (by omega) b⟩
  else if hm : (i + 1) + 2 * (j + 1) ≤ depth then
    ⟨arithmeticTargetWiderBoundaryOutputChart node data m k hk i j hi hj
        hij hm (by omega) (by omega) b,
      arithmeticTargetWiderBoundaryQuotientOutput node data m k hk i j hi hj
        hij hm (by omega) (by omega) b⟩
  else
    ⟨arithmeticTargetReflectedOutputChart node data m k hk i j hi hj
        hij hpre (by omega) (by omega) b,
      arithmeticTargetReflectedQuotientOutput node data m k hk i j hi hj
        hij hpre (by omega) (by omega) b⟩

/-- Each selected domain is an actual open of the original ordered target pair. -/
def arithmeticTargetFlexiblePreMiddleChart (b : Fin 3) : (pullback f g).Opens :=
  (arithmeticTargetFlexiblePreMiddleData node data m k hk i j hi hj hij hpre hstage b).1

local notation "D" => arithmeticTargetFlexiblePreMiddleChart
  node data m k hk i j hi hj hij hpre hstage

/-- The whole quotient-valued output on the selected domain. -/
def arithmeticTargetFlexiblePreMiddleOutput (b : Fin 3) : (D b).toScheme ⟶ pullback q t :=
  (arithmeticTargetFlexiblePreMiddleData node data m k hk i j hi hj hij hpre hstage b).2

/-- Every branch retains the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticTargetFlexiblePreMiddleOutput_base (b : Fin 3) :
    arithmeticTargetFlexiblePreMiddleOutput node data m k hk i j hi hj hij hpre hstage b ≫
      pullback.fst q t = (D b).ι ≫ pullback.fst f g ≫ f := by
  classical
  let property (v : Σ O : (pullback f g).Opens, O.toScheme ⟶ pullback q t) : Prop :=
    v.2 ≫ pullback.fst q t = v.1.ι ≫ pullback.fst f g ≫ f
  change property
    (arithmeticTargetFlexiblePreMiddleData node data m k hk i j hi hj hij hpre hstage b)
  unfold arithmeticTargetFlexiblePreMiddleData
  split_ifs with hs hm
  · exact arithmeticTargetFactoredSumQuotientOutput_base node data m k hk i j hi hj
      hij (by omega) (by omega) b
  · exact arithmeticTargetWiderBoundaryQuotientOutput_base node data m k hk i j hi hj
      hij hm (by omega) (by omega) b
  · exact arithmeticTargetReflectedQuotientOutput_base node data m k hk i j hi hj
      hij hpre (by omega) (by omega) b

/-- All punctured unequal targets before the middle reach a genuine formula domain. -/
theorem arithmeticTargetFlexiblePreMiddleChart_punctured (hlt : i < j)
    (p : (pullback f g : Scheme))
    (hx : tensorCoord W (π ^ (0 + (i + 1))) π (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2 ∉
      (I (pullback.fst f g p)).asIdeal)
    (hy : tensorCoord W (π ^ (0 + (j + 1))) π (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2 ∉
      (J (pullback.snd f g p)).asIdeal) : ∃ b, p ∈ D b := by
  classical
  unfold arithmeticTargetFlexiblePreMiddleChart arithmeticTargetFlexiblePreMiddleData
  split_ifs with hs hm
  · exact arithmeticTargetFactoredSumOutputChart_punctured node data m k hk i j hi hj
      hij (by omega) (by omega) hs hlt p hx hy
  · exact arithmeticTargetWiderBoundaryOutputChart_punctured node data m k hk i j hi hj
      hij hm (by omega) (by omega) hlt p hx hy
  · exact arithmeticTargetReflectedOutputChart_punctured node data m k hk i j hi hj
      hij hpre (by omega) (by omega) hlt p hx hy

end FLT.Mazur.WeierstrassDividedDepth
