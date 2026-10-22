/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairSourceCover
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMiddleLocal
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroOddLocalCover
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroSelfLocalCover
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroSelfOddLocalCover

/-!
# Stage-one inner pairs on one smooth-product presentation

The retained self-pair and retained/terminal pair have actual output covers
at node depths two and three. All coefficients remain in the original quotient.
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
  (m : ℕ) (hi : 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data 1 hi
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m 1 hi
local notation "s" => finiteGlobalArithmeticStructure hπ data 1 hi m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q 1 hi
local notation "fa" => (O 2).ι ≫ chart 2 ≫ s
local notation "fb" => (O 1).ι ≫ chart 1 ≫ s
variable (hgen : IsLocalRing.maximalIdeal R = ideal R π)
include hgen

/-- The complete stage-one selfmiddle pair is covered by constructed quotient outputs. -/
theorem arithmeticStageOneSelfMiddleOutputCover (hm : 2 = depth) :
    ∃ (C : (pullback fa fa : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫ pullback.fst fa fa ≫ fa := by
  exact arithmeticSmoothPairSource_outputCover hπ data m 1 hi 2 2
    (arithmeticLastRetainedZeroSelfLocalSource node data m hi)
    (arithmeticLastRetainedZeroSelfLocalInclusion node data m hi)
    (arithmeticLastRetainedZeroSelfLocal_exists node data m hi hm hgen)
    (arithmeticLastRetainedZeroSelfLocalOutput node data m hi hm)
    (arithmeticLastRetainedZeroSelfLocalOutput_base node data m hi hm)

/-- The complete stage-one selfodd pair is covered by constructed quotient outputs. -/
theorem arithmeticStageOneSelfOddOutputCover (hm : depth = 3) :
    ∃ (C : (pullback fa fa : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫ pullback.fst fa fa ≫ fa := by
  exact arithmeticSmoothPairSource_outputCover hπ data m 1 hi 2 2
    (arithmeticLastRetainedZeroSelfOddLocalSource node data m hi hm)
    (arithmeticLastRetainedZeroSelfOddLocalInclusion node data m hi hm)
    (arithmeticLastRetainedZeroSelfOddLocal_exists node data m hi hm hgen)
    (arithmeticLastRetainedZeroSelfOddLocalOutput node data m hi hm)
    (arithmeticLastRetainedZeroSelfOddLocalOutput_base node data m hi hm)

/-- The complete stage-one mixedmiddle pair is covered by constructed quotient outputs. -/
theorem arithmeticStageOneMixedMiddleOutputCover (hm : 2 = depth) :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫ pullback.fst fa fb ≫ fa := by
  exact arithmeticSmoothPairSource_outputCover hπ data m 1 hi 2 1
    (arithmeticLastRetainedMiddleLocalSource node data m 0 hi)
    (arithmeticLastRetainedMiddleLocalInclusion node data m 0 hi)
    (arithmeticLastRetainedMiddleLocal_exists node data m 0 hi hm hgen)
    (arithmeticLastRetainedMiddleLocalOutput node data m 0 hi hm)
    (arithmeticLastRetainedMiddleLocalOutput_base node data m 0 hi hm)

/-- The complete stage-one mixedodd pair is covered by constructed quotient outputs. -/
theorem arithmeticStageOneMixedOddOutputCover (hm : depth = 3) :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫ pullback.fst fa fb ≫ fa := by
  exact arithmeticSmoothPairSource_outputCover hπ data m 1 hi 2 1
    (arithmeticLastRetainedZeroOddLocalSource node data m 0 hi hm)
    (arithmeticLastRetainedZeroOddLocalInclusion node data m 0 hi hm)
    (arithmeticLastRetainedZeroOddLocal_exists node data m 0 hi hm hgen rfl)
    (arithmeticLastRetainedZeroOddLocalOutput node data m 0 hi hm)
    (arithmeticLastRetainedZeroOddLocalOutput_base node data m 0 hi hm)

/-- Both boundary node depths give a complete stage-one self output cover. -/
theorem arithmeticStageOneSelfOutputCover (hd : depth = 2 ∨ depth = 3) :
    ∃ (C : (pullback fa fa : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫ pullback.fst fa fa ≫ fa := by
  rcases hd with hd | hd
  · exact arithmeticStageOneSelfMiddleOutputCover node data m hi hgen hd.symm
  · exact arithmeticStageOneSelfOddOutputCover node data m hi hgen hd

/-- Both boundary node depths give a complete stage-one mixed output cover. -/
theorem arithmeticStageOneMixedOutputCover (hd : depth = 2 ∨ depth = 3) :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (i : C.I₀) → C.X i ⟶ pullback q t),
      ∀ i, out i ≫ pullback.fst q t = C.f i ≫ pullback.fst fa fb ≫ fa := by
  rcases hd with hd | hd
  · exact arithmeticStageOneMixedMiddleOutputCover node data m hi hgen hd.symm
  · exact arithmeticStageOneMixedOddOutputCover node data m hi hgen hd

end FLT.Mazur.WeierstrassDividedDepth
