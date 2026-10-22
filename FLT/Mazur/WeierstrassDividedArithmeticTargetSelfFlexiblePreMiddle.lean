/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfQuadrupleAddition
public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfIntermediateAddition
public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfShallowAddition

/-!
# Pre-middle equal targets with the actual required output stage

Choose the actual deep, quadruple, intermediate or shallow formula according
to node depth. Together with the reciprocal output this covers all punctured
equal targets strictly before the middle depth. The final stage need contain
only the smaller of the doubled depth and its reflected depth.
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
  (hstage : min (2 * (i + 1)) (depth - 2 * (i + 1)) ≤ k) (hpre : 2 * (i + 1) < depth)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "f" => chart c ≫ s
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local notation "t" => (U).ι ≫ base

/-- Select a genuine formula together with its actual domain, without transporting types. -/
def arithmeticTargetSelfFlexiblePreMiddleData :
    Σ O : (pullback f f).Opens, O.toScheme ⟶ pullback q t :=
  if _hd : 4 * (i + 1) < depth then
    ⟨arithmeticTargetSelfDeepOpen node data m k hk i hi (by omega),
      arithmeticTargetSelfDeepQuotientOutput node data m k hk i hi (by omega)⟩
  else if hq : depth = 4 * (i + 1) then
    ⟨arithmeticTargetSelfQuadrupleOpen node data m k hk i hi hq,
      arithmeticTargetSelfQuadrupleQuotientOutput node data m k hk i hi (by omega) hq⟩
  else if hm : 3 * (i + 1) ≤ depth then
    ⟨arithmeticTargetSelfIntermediateOpen node data m k hk i hi hm (by omega) (by omega),
      arithmeticTargetSelfIntermediateQuotientOutput node data m k hk i hi
        hm (by omega) (by omega)⟩
  else
    ⟨arithmeticTargetSelfShallowOpen node data m k hk i hi hpre (by omega) (by omega),
      arithmeticTargetSelfShallowQuotientOutput node data m k hk i hi
        hpre (by omega) (by omega)⟩

/-- The selected formula's actual domain at the original node depth. -/
def arithmeticTargetSelfFlexiblePreMiddleOpen : (pullback f f).Opens :=
  (arithmeticTargetSelfFlexiblePreMiddleData node data m k hk i hi hstage hpre).1

local notation "D" => arithmeticTargetSelfFlexiblePreMiddleOpen node data m k hk i hi hstage hpre
local notation "C" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi

/-- The selected formula retains its complete quotient-valued smooth output. -/
def arithmeticTargetSelfFlexiblePreMiddleQuotientOutput : (D).toScheme ⟶ pullback q t :=
  (arithmeticTargetSelfFlexiblePreMiddleData node data m k hk i hi hstage hpre).2

/-- All four ranges preserve the exact original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticTargetSelfFlexiblePreMiddleQuotientOutput_base :
    arithmeticTargetSelfFlexiblePreMiddleQuotientOutput node data m k hk i hi hstage hpre ≫
      pullback.fst q t = (D).ι ≫ pullback.fst f f ≫ f := by
  classical
  let property (v : Σ O : (pullback f f).Opens, O.toScheme ⟶ pullback q t) : Prop :=
    v.2 ≫ pullback.fst q t = v.1.ι ≫ pullback.fst f f ≫ f
  change property (arithmeticTargetSelfFlexiblePreMiddleData node data m k hk i hi hstage hpre)
  unfold arithmeticTargetSelfFlexiblePreMiddleData
  split_ifs with hd hq hm
  · exact arithmeticTargetSelfDeepQuotientOutput_base node data m k hk i hi (by omega)
  · exact arithmeticTargetSelfQuadrupleQuotientOutput_base node data m k hk i hi (by omega) hq
  · exact arithmeticTargetSelfIntermediateQuotientOutput_base node data m k hk i hi
      hm (by omega) (by omega)
  · exact arithmeticTargetSelfShallowQuotientOutput_base node data m k hk i hi
      hpre (by omega) (by omega)

local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2

/-- Every punctured equal pair before the middle reaches a whole resolved output. -/
theorem arithmeticTargetSelfFlexiblePreMiddle_punctured_cover (p : (pullback f f : Scheme))
    (hx : u ∉ (I (pullback.fst f f p)).asIdeal)
    (hy : u ∉ (I (pullback.snd f f p)).asIdeal) : p ∈ D ∨ p ∈ C := by
  classical
  unfold arithmeticTargetSelfFlexiblePreMiddleOpen arithmeticTargetSelfFlexiblePreMiddleData
  split_ifs with hd hq hm
  · exact arithmeticTargetSelfDeep_punctured_cover node data m k hk i hi (by omega) hd p hx hy
  · exact arithmeticTargetSelfQuadruple_punctured_cover node data m k hk i hi hq p hx hy
  · exact arithmeticTargetSelfIntermediate_punctured_cover node data m k hk i hi
      hm (by omega) (by omega) p hx hy
  · exact arithmeticTargetSelfShallow_punctured_cover node data m k hk i hi
      hpre (by omega) (by omega) p hx hy

end FLT.Mazur.WeierstrassDividedDepth
