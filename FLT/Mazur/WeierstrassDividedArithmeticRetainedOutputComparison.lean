/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedInputComparison
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSmoothAddition
public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairAddition
public import FLT.Mazur.WeierstrassDividedOlderNegativeSumDepthAddition
public import FLT.Mazur.SchemeRestrictedOutputComparison

/-!
# Outputs agree through the original retained boundary transition

The three arithmetic constructions on the original smooth transition source
agree with the existing integral atlas outputs after the canonical transition.
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
  arithmeticFixedAdjacentTargetCoordinates arithmeticTargetPairSpectrumIso
  arithmeticTargetSmoothPairInclusion arithmeticAtlasPairPresentation olderUnequalFormulaInput
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
  (hij : i ≤ j) (hdepth : 4 * (j + 1) ≤ depth)
  (hsum : (i + 1) + (j + 1) ≤ k) (h2 : W.a₂ = 0)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "c" => retainedOlderFormulaIndex k (i + 1) (Nat.lt_of_succ_le hi)
local notation "d" => retainedOlderFormulaIndex k (j + 1) (Nat.lt_of_succ_le hj)
local notation "di" => data ⟨i + 1, Nat.lt_succ_of_le ((Nat.le_succ (i + 1)).trans (hi.trans hk))⟩
local notation "dj" => data ⟨j + 1, Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk
local notation "fa" => (O c).ι ≫ chart c ≫ s
local notation "fb" => (O d).ι ≫ chart d ≫ s
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
local notation "coords" => tensorIntegralAtlasProjection hπ data Q k hk
local notation "f" => retainedOlderLowerCoordinates hπ data k hk (i + 1) (Nat.lt_of_succ_le hi)
  (i + 1) le_rfl
local notation "g" => retainedOlderLowerCoordinates hπ data k hk (j + 1) (Nat.lt_of_succ_le hj)
  (j + 1) le_rfl
local notation "input" => Spec.map
  (CommRingCat.ofHom (successiveTensorPairInput hπ di ei dj ej Q).toRingHom)
local notation "P" => arithmeticAtlasPairPresentation hπ data m k hk c d
local notation "F" => olderUnequalFormulaInput hπ data k hk (i + 1) (j + 1)
  (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj)

local notation "a" => (Fin.succ ⟨k - i, by omega⟩ : Fin (k + 3))
local notation "b" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "smoothSource" => arithmeticRetainedDoubleSmoothOpen hπ data m k hk i j hi hj
local notation "tr" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj
local notation "transition" => arithmeticRetainedDoubleTransition hπ data m k hk i j hi hj
local notation "transfer" => atlasPairTransfer hπ data k hk a b c d
local notation "sourceMap" => (smoothSource).ι ≫ tr
local notation "integralMap" => transition ≫ transfer
local notation "H" => arithmeticRetainedSmooth_input hπ data m k hk i j hi hj
local notation "dd" => olderSumDepthDoubledData node (i + 1)
  ((Nat.mul_le_mul_left 4 (Nat.add_le_add_right hij 1)).trans hdepth)
local notation "ee" => olderSumDepthDoubledData node (j + 1) hdepth
local notation "hkl" => Nat.add_le_add_left (Nat.add_le_add_right hij 1) 0
local notation "hs" => (Nat.add_le_add (Nat.le_of_eq (Nat.zero_add (i + 1)))
  (Nat.le_of_eq (Nat.zero_add (j + 1)))).trans hsum
local notation "al" => unequalPairLeft di dj
local notation "ar" => unequalPairRight di dj
local notation "hdiff" => (Nat.sub_le (0 + (j + 1)) (0 + (i + 1))).trans
  ((Nat.le_of_eq (Nat.zero_add (j + 1))).trans (Nat.lt_of_succ_le hj).le)

local notation "TPositive" => arithmeticTargetPairPositiveOpen
      node data m k hk i j hi hj hij hdepth hsum h2
local notation "VPositive" => olderSumDepthOpen node data k hk (i + 1) (j + 1)
  (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) hdepth hsum h2
local notation "OPositive" => sumDepthDomain hπ di dj hkl data ((hs).trans hk) dd ee h2 al ar

/-- The complete positive domains agree on the original smooth transition source. -/
theorem arithmeticRetainedIntegralPositiveOpen_eq :
    arithmeticRetainedSmoothPositiveOpen node data m k hk i j hi hj hij hdepth hsum h2 =
      integralMap ⁻¹ᵁ VPositive := by
  simpa only [arithmeticRetainedSmoothPositiveOpen, arithmeticTargetPairPositiveOpen,
    successiveTensorPairPositiveOpen, olderSumDepthOpen, atlasPairSumDepthOpen,
    olderUnequalFormulaInput, Scheme.Hom.comp_preimage] using
    SchemeRestrictedOutputComparison.domain_eq (sourceMap ≫ (E).hom) integralMap input F
    (by simpa only [Category.assoc, retainedOlderFormulaIndex, Fin.succ] using H) OPositive

/-- The constructed positive outputs agree as morphisms into the same smooth model. -/
theorem arithmeticRetainedIntegralPositiveAddition_eq :
    ((smoothSource).toScheme).homOfLE
        (arithmeticRetainedIntegralPositiveOpen_eq node data m k hk i j hi hj hij
          hdepth hsum h2).le ≫
      (integralMap ∣_ VPositive) ≫ olderSumDepthAddition node data k hk (i + 1) (j + 1)
        (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) hdepth hsum h2 =
        arithmeticRetainedSmoothPositiveAddition
      node data m k hk i j hi hj hij hdepth hsum h2 := by
  simpa only [olderSumDepthAddition, atlasPairSumDepthAddition,
    olderSumDepthOpen, atlasPairSumDepthOpen, arithmeticTargetPairPositiveOpen,
    successiveTensorPairPositiveOpen, Scheme.Hom.comp_preimage,
    arithmeticRetainedSmoothPositiveOpen,
    arithmeticRetainedSmoothPositiveAddition, arithmeticTargetPairPositiveAddition,
    successiveTensorPairPositiveAddition,
    olderUnequalFormulaInput, morphismRestrict_comp, Category.assoc] using
    SchemeRestrictedOutputComparison.output_eq (sourceMap ≫ (E).hom) integralMap input F
      (by simpa only [Category.assoc, retainedOlderFormulaIndex, Fin.succ] using H) OPositive
      (sumDepthResolvedAddition hπ di dj hkl data ((hs).trans hk)
      dd ee h2 al ar k hk hs)

local notation "TNegative" => arithmeticTargetPairNegativeOpen
      node data m k hk i j hi hj hij hdepth hsum h2
local notation "VNegative" => olderNegativeSumDepthOpen node data k hk (i + 1) (j + 1)
  (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) hdepth hsum h2
local notation "ONegative" => negativeSumDepthDomain hπ di dj hkl data
  ((hs).trans hk) dd ee h2 al ar

/-- The complete negative domains agree on the original smooth transition source. -/
theorem arithmeticRetainedIntegralNegativeOpen_eq :
    arithmeticRetainedSmoothNegativeOpen node data m k hk i j hi hj hij hdepth hsum h2 =
      integralMap ⁻¹ᵁ VNegative := by
  simpa only [arithmeticRetainedSmoothNegativeOpen, arithmeticTargetPairNegativeOpen,
    successiveTensorPairNegativeOpen, olderNegativeSumDepthOpen, atlasPairNegativeSumDepthOpen,
    olderUnequalFormulaInput, Scheme.Hom.comp_preimage] using
    SchemeRestrictedOutputComparison.domain_eq (sourceMap ≫ (E).hom) integralMap input F
    (by simpa only [Category.assoc, retainedOlderFormulaIndex, Fin.succ] using H) ONegative

/-- The constructed negative outputs agree as morphisms into the same smooth model. -/
theorem arithmeticRetainedIntegralNegativeAddition_eq :
    ((smoothSource).toScheme).homOfLE
        (arithmeticRetainedIntegralNegativeOpen_eq node data m k hk i j hi hj hij
          hdepth hsum h2).le ≫
      (integralMap ∣_ VNegative) ≫ olderNegativeSumDepthAddition node data k hk (i + 1) (j + 1)
        (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) hdepth hsum h2 =
        arithmeticRetainedSmoothNegativeAddition
      node data m k hk i j hi hj hij hdepth hsum h2 := by
  simpa only [olderNegativeSumDepthAddition, atlasPairNegativeSumDepthAddition,
    olderNegativeSumDepthOpen, atlasPairNegativeSumDepthOpen, arithmeticTargetPairNegativeOpen,
    successiveTensorPairNegativeOpen, Scheme.Hom.comp_preimage,
    arithmeticRetainedSmoothNegativeOpen,
    arithmeticRetainedSmoothNegativeAddition, arithmeticTargetPairNegativeAddition,
    successiveTensorPairNegativeAddition,
    olderUnequalFormulaInput, morphismRestrict_comp, Category.assoc] using
    SchemeRestrictedOutputComparison.output_eq (sourceMap ≫ (E).hom) integralMap input F
      (by simpa only [Category.assoc, retainedOlderFormulaIndex, Fin.succ] using H) ONegative
      (negativeSumDepthAddition hπ di dj hkl data ((hs).trans hk)
      dd ee h2 al ar k hk hs)

local notation "TOpposite" => arithmeticTargetPairOppositeOpen node data m k hk i j hi hj hij hsum
local notation "VOpposite" => olderUnequalOpen hπ data k hk (i + 1) (j + 1)
  (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1)
local notation "OOpposite" => unequalDepthDomain hπ di dj hkl data ((hdiff).trans hk) al ar

/-- The complete opposite domains agree on the original smooth transition source. -/
theorem arithmeticRetainedIntegralOppositeOpen_eq :
    arithmeticRetainedSmoothOppositeOpen node data m k hk i j hi hj hij hsum =
      integralMap ⁻¹ᵁ VOpposite := by
  simpa only [arithmeticRetainedSmoothOppositeOpen, arithmeticTargetPairOppositeOpen,
    successiveTensorPairOppositeOpen, olderUnequalOpen, atlasPairUnequalOpen,
    olderUnequalFormulaInput, Scheme.Hom.comp_preimage] using
    SchemeRestrictedOutputComparison.domain_eq (sourceMap ≫ (E).hom) integralMap input F
    (by simpa only [Category.assoc, retainedOlderFormulaIndex, Fin.succ] using H) OOpposite

/-- The constructed opposite outputs agree as morphisms into the same smooth model. -/
theorem arithmeticRetainedIntegralOppositeAddition_eq :
    ((smoothSource).toScheme).homOfLE
        (arithmeticRetainedIntegralOppositeOpen_eq node data m k hk i j hi hj hij
          hsum).le ≫
      (integralMap ∣_ VOpposite) ≫ olderUnequalAddition hπ data k hk (i + 1) (j + 1)
        (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) =
        arithmeticRetainedSmoothOppositeAddition
      node data m k hk i j hi hj hij hsum := by
  simpa only [olderUnequalAddition, atlasPairUnequalAddition,
    olderUnequalOpen, atlasPairUnequalOpen, arithmeticTargetPairOppositeOpen,
    successiveTensorPairOppositeOpen, Scheme.Hom.comp_preimage,
    arithmeticRetainedSmoothOppositeOpen,
    arithmeticRetainedSmoothOppositeAddition, arithmeticTargetPairOppositeAddition,
    successiveTensorPairOppositeAddition,
    olderUnequalFormulaInput, morphismRestrict_comp, Category.assoc] using
    SchemeRestrictedOutputComparison.output_eq (sourceMap ≫ (E).hom) integralMap input F
      (by simpa only [Category.assoc, retainedOlderFormulaIndex, Fin.succ] using H) OOpposite
      (unequalDepthResolvedAddition hπ di dj hkl data ((hdiff).trans hk) al ar k hk hdiff)

end FLT.Mazur.WeierstrassDividedDepth
