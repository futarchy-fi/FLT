/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedBoundaryNodalReversed
public import FLT.Mazur.WeierstrassDividedArithmeticMixedZeroBoundaryNodalReversed
public import FLT.Mazur.WeierstrassDividedDepthFeasibility

/-!
# Full mixed boundary covers at the maximal stage

The supplied division family and maximal-stage bound discharge all depth
premises. Both input orders have full smooth covers, including creation zero,
provided the next retained chart exists. Original inputs need no puncture.
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
  arithmeticFixedAdjacentPairOpen arithmeticFixedAdjacentPairTransfer
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k + 2 ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => (Fin.succ ⟨j - k,
  Nat.lt_succ_of_le ((Nat.sub_le j k).trans (Nat.le_succ j))⟩ : Fin (j + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
local notation "f" => chart a ≫ s
local notation "g" => chart 1 ≫ s
variable (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hmax : depth ≤ 2 * j + 1)
local notation "hd" => dataFamily_twice_stage_le node data j hj
local notation "A" => arithmeticMixedBoundaryNodalSmoothOpen node data m j hj k
local notation "B" => arithmeticMixedBoundaryNodalReversedSmoothOpen node data m j hj k
local notation "Z" => arithmeticMixedZeroBoundaryNodalSmoothOpen node data m j hj k
local notation "Y" => arithmeticMixedZeroBoundaryNodalReversedSmoothOpen node data m j hj k

/-- A positive nonlast retained input and the terminal input have a full maximal-stage cover. -/
def arithmeticMixedBoundaryMaximalCover (hk0 : 0 < k) : (A).toScheme.OpenCover :=
  arithmeticMixedBoundaryNodalSmoothCover node data m j hj k hk hd (by omega) hgen hk0

/-- Every chart in the maximal-stage cover has its entire quotient-valued output. -/
def arithmeticMixedBoundaryMaximalOutput (hk0 : 0 < k) (c : MixedBoundaryNodalLocalIndex) :
    (arithmeticMixedBoundaryMaximalCover node data m j hj k hk hgen hmax hk0).X c ⟶
      pullback q t :=
  arithmeticMixedBoundaryNodalSmoothOutput node data m j hj k hk hd (by omega) c

/-- Maximal-stage output retains all original arithmetic coefficients. -/
@[reassoc] theorem arithmeticMixedBoundaryMaximalOutput_base
    (hk0 : 0 < k) (c : MixedBoundaryNodalLocalIndex) :
    arithmeticMixedBoundaryMaximalOutput node data m j hj k hk hgen hmax hk0 c ≫
      pullback.fst q t =
      (arithmeticMixedBoundaryMaximalCover node data m j hj k hk hgen hmax hk0).f c ≫
        (A).ι ≫ pullback.fst f g ≫ f :=
  arithmeticMixedBoundaryNodalSmoothOutput_base node data m j hj k hk hd (by omega) c

/-- The full positive retained/terminal cover also exists in the reverse order. -/
def arithmeticMixedBoundaryMaximalReversedCover (hk0 : 0 < k) : (B).toScheme.OpenCover :=
  arithmeticMixedBoundaryNodalReversedSmoothCover node data m j hj k hk hd (by omega) hgen hk0

/-- Reversed maximal-stage charts carry their whole constructed output. -/
def arithmeticMixedBoundaryMaximalReversedOutput
    (hk0 : 0 < k) (c : MixedBoundaryNodalLocalIndex) :
    (arithmeticMixedBoundaryMaximalReversedCover node data m j hj k hk hgen hmax hk0).X c ⟶
      pullback q t :=
  arithmeticMixedBoundaryNodalReversedSmoothOutput node data m j hj k hk hd (by omega) c

/-- Reversed positive outputs preserve the original terminal coefficient morphism. -/
@[reassoc] theorem arithmeticMixedBoundaryMaximalReversedOutput_base
    (hk0 : 0 < k) (c : MixedBoundaryNodalLocalIndex) :
    arithmeticMixedBoundaryMaximalReversedOutput node data m j hj k hk hgen hmax hk0 c ≫
      pullback.fst q t =
      (arithmeticMixedBoundaryMaximalReversedCover node data m j hj k hk hgen hmax hk0).f c ≫
        (B).ι ≫ pullback.fst g f ≫ g :=
  arithmeticMixedBoundaryNodalReversedSmoothOutput_base node data m j hj k hk hd (by omega) c

/-- Creation zero also has a full maximal-stage cover whenever its transfer exists. -/
def arithmeticMixedZeroBoundaryMaximalCover (hk0 : k = 0) : (Z).toScheme.OpenCover :=
  arithmeticMixedZeroBoundaryNodalSmoothCover node data m j hj k hk hd (by omega) hgen hk0

/-- Creation-zero charts retain their genuine difference or transferred normalized output. -/
def arithmeticMixedZeroBoundaryMaximalOutput
    (hk0 : k = 0) (c : MixedZeroBoundaryNodalLocalIndex) :
    (arithmeticMixedZeroBoundaryMaximalCover node data m j hj k hk hgen hmax hk0).X c ⟶
      pullback q t :=
  arithmeticMixedZeroBoundaryNodalSmoothOutput node data m j hj k hk hd (by omega) c

/-- The zero-created maximal-stage output preserves the full original coefficient morphism. -/
@[reassoc] theorem arithmeticMixedZeroBoundaryMaximalOutput_base
    (hk0 : k = 0) (c : MixedZeroBoundaryNodalLocalIndex) :
    arithmeticMixedZeroBoundaryMaximalOutput node data m j hj k hk hgen hmax hk0 c ≫
      pullback.fst q t =
      (arithmeticMixedZeroBoundaryMaximalCover node data m j hj k hk hgen hmax hk0).f c ≫
        (Z).ι ≫ pullback.fst f g ≫ f :=
  arithmeticMixedZeroBoundaryNodalSmoothOutput_base node data m j hj k hk hd (by omega) c

/-- Creation-zero retained/terminal inputs have a full cover in the reverse order. -/
def arithmeticMixedZeroBoundaryMaximalReversedCover (hk0 : k = 0) : (Y).toScheme.OpenCover :=
  arithmeticMixedZeroBoundaryNodalReversedSmoothCover
    node data m j hj k hk hd (by omega) hgen hk0

/-- Every reversed creation-zero chart carries its entire arithmetic quotient output. -/
def arithmeticMixedZeroBoundaryMaximalReversedOutput
    (hk0 : k = 0) (c : MixedZeroBoundaryNodalLocalIndex) :
    (arithmeticMixedZeroBoundaryMaximalReversedCover node data m j hj k hk hgen hmax hk0).X c ⟶
      pullback q t :=
  arithmeticMixedZeroBoundaryNodalReversedSmoothOutput node data m j hj k hk hd (by omega) c

/-- Reversed zero-created outputs also preserve the whole coefficient morphism. -/
@[reassoc] theorem arithmeticMixedZeroBoundaryMaximalReversedOutput_base
    (hk0 : k = 0) (c : MixedZeroBoundaryNodalLocalIndex) :
    arithmeticMixedZeroBoundaryMaximalReversedOutput node data m j hj k hk hgen hmax hk0 c ≫
      pullback.fst q t =
      (arithmeticMixedZeroBoundaryMaximalReversedCover
        node data m j hj k hk hgen hmax hk0).f c ≫
        (Y).ι ≫ pullback.fst g f ≫ g :=
  arithmeticMixedZeroBoundaryNodalReversedSmoothOutput_base
    node data m j hj k hk hd (by omega) c

end FLT.Mazur.WeierstrassDividedDepth
