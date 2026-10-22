/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedZeroShortSmoothCover
public import FLT.Mazur.WeierstrassDividedDepthFeasibility

/-!
# Creation-zero coverage from the actual supplied stage alone

At stage at least two the supplied division data already force node depth
at least four. The five-source cover therefore needs no independent node-depth
or later-stage premise. In particular it applies at stage two for depths four
and five whenever the stated node and division data are supplied.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (hstage : 2 ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "c" => (Fin.succ ⟨k - 0,
  Nat.lt_succ_of_le ((Nat.sub_le k 0).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "t" => (base).smoothLocus.ι ≫ base

omit [IsDomain R] [IsBezout R] [IsNoetherianRing R] in
include node data hk hstage in
/-- The actual stage data supply the strict depth bound needed by the double transfer. -/
theorem arithmeticRetainedZeroStageTwo_depth : 2 * (0 + 1) < depth := by
  have h := dataFamily_twice_stage_le node data k hk
  omega

local notation "hd" => arithmeticRetainedZeroStageTwo_depth node data k hk hstage
local notation "U" => arithmeticRetainedZeroShortSmoothPairOpen node data m k hk 0

/-- The constructed five-source cover requires only the original selected stage bound. -/
def arithmeticRetainedZeroStageTwoCover : (U).toScheme.OpenCover :=
  arithmeticRetainedZeroShortSmoothCover node data m k hk 0 hstage hstage hd
    rfl node.maximalIdeal_eq

/-- Every member carries its original quotient-valued resolved sum. -/
def arithmeticRetainedZeroStageTwoOutput (b : RetainedZeroShortLocalIndex) :
    (arithmeticRetainedZeroStageTwoCover node data m k hk hstage).X b ⟶ pullback q t :=
  arithmeticRetainedZeroShortSmoothLocalOutput node data m k hk 0 hstage hstage hd b

/-- The sum keeps the original coefficient point of the smooth input pair. -/
@[reassoc] theorem arithmeticRetainedZeroStageTwoOutput_base
    (b : RetainedZeroShortLocalIndex) :
    arithmeticRetainedZeroStageTwoOutput node data m k hk hstage b ≫ pullback.fst q t =
      (arithmeticRetainedZeroStageTwoCover node data m k hk hstage).f b ≫
        (U).ι ≫ pullback.fst f f ≫ f :=
  arithmeticRetainedZeroShortSmoothLocalOutput_base node data m k hk 0 hstage hstage hd b

end FLT.Mazur.WeierstrassDividedDepth
