/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetInputComparison
public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairAddition
public import FLT.Mazur.WeierstrassDividedOlderNegativeSumDepthAddition
public import FLT.Mazur.SchemeRestrictedOutputComparison

/-!
# Arithmetic and integral retained-pair outputs agree

The positive, negative, and opposite output domains agree under the original
smooth arithmetic presentation, and their constructed smooth outputs coincide.
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

local notation "inc" => arithmeticTargetSmoothPairInclusion hπ data m k hk i j hi hj
local notation "H" => arithmeticTargetSmoothPair_input hπ data m k hk i j hi hj
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

/-- The complete positive domains agree in the original smooth arithmetic pair. -/
theorem arithmeticTargetSmoothPositiveOpen_eq :
    inc ⁻¹ᵁ TPositive = P ⁻¹ᵁ VPositive := by
  simpa only [arithmeticTargetPairPositiveOpen,
    successiveTensorPairPositiveOpen, olderSumDepthOpen, atlasPairSumDepthOpen,
    olderUnequalFormulaInput, Scheme.Hom.comp_preimage] using
    SchemeRestrictedOutputComparison.domain_eq (inc ≫ (E).hom) P input F
    (by simpa only [Category.assoc] using H) OPositive

/-- The constructed positive outputs agree as morphisms into the same smooth model. -/
theorem arithmeticTargetSmoothPositiveAddition_eq :
    (pullback fa fb : Scheme).homOfLE
        (arithmeticTargetSmoothPositiveOpen_eq node data m k hk i j hi hj hij hdepth hsum h2).le ≫
      (P ∣_ VPositive) ≫ olderSumDepthAddition node data k hk (i + 1) (j + 1)
        (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) hdepth hsum h2 =
        (inc ∣_ TPositive) ≫ arithmeticTargetPairPositiveAddition
      node data m k hk i j hi hj hij hdepth hsum h2 := by
  simpa only [olderSumDepthAddition, atlasPairSumDepthAddition,
    olderSumDepthOpen, atlasPairSumDepthOpen, arithmeticTargetPairPositiveOpen,
    successiveTensorPairPositiveOpen, Scheme.Hom.comp_preimage,
    arithmeticTargetPairPositiveAddition, successiveTensorPairPositiveAddition,
    olderUnequalFormulaInput, morphismRestrict_comp, Category.assoc] using
    SchemeRestrictedOutputComparison.output_eq (inc ≫ (E).hom) P input F
      (by simpa only [Category.assoc] using H) OPositive
      (sumDepthResolvedAddition hπ di dj hkl data ((hs).trans hk)
      dd ee h2 al ar k hk hs)

local notation "TNegative" => arithmeticTargetPairNegativeOpen
      node data m k hk i j hi hj hij hdepth hsum h2
local notation "VNegative" => olderNegativeSumDepthOpen node data k hk (i + 1) (j + 1)
  (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) hdepth hsum h2
local notation "ONegative" => negativeSumDepthDomain hπ di dj hkl data
  ((hs).trans hk) dd ee h2 al ar

/-- The complete negative domains agree in the original smooth arithmetic pair. -/
theorem arithmeticTargetSmoothNegativeOpen_eq :
    inc ⁻¹ᵁ TNegative = P ⁻¹ᵁ VNegative := by
  simpa only [arithmeticTargetPairNegativeOpen,
    successiveTensorPairNegativeOpen, olderNegativeSumDepthOpen, atlasPairNegativeSumDepthOpen,
    olderUnequalFormulaInput, Scheme.Hom.comp_preimage] using
    SchemeRestrictedOutputComparison.domain_eq (inc ≫ (E).hom) P input F
    (by simpa only [Category.assoc] using H) ONegative

/-- The constructed negative outputs agree as morphisms into the same smooth model. -/
theorem arithmeticTargetSmoothNegativeAddition_eq :
    (pullback fa fb : Scheme).homOfLE
        (arithmeticTargetSmoothNegativeOpen_eq node data m k hk i j hi hj hij hdepth hsum h2).le ≫
      (P ∣_ VNegative) ≫ olderNegativeSumDepthAddition node data k hk (i + 1) (j + 1)
        (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1) hdepth hsum h2 =
        (inc ∣_ TNegative) ≫ arithmeticTargetPairNegativeAddition
      node data m k hk i j hi hj hij hdepth hsum h2 := by
  simpa only [olderNegativeSumDepthAddition, atlasPairNegativeSumDepthAddition,
    olderNegativeSumDepthOpen, atlasPairNegativeSumDepthOpen, arithmeticTargetPairNegativeOpen,
    successiveTensorPairNegativeOpen, Scheme.Hom.comp_preimage,
    arithmeticTargetPairNegativeAddition, successiveTensorPairNegativeAddition,
    olderUnequalFormulaInput, morphismRestrict_comp, Category.assoc] using
    SchemeRestrictedOutputComparison.output_eq (inc ≫ (E).hom) P input F
      (by simpa only [Category.assoc] using H) ONegative
      (negativeSumDepthAddition hπ di dj hkl data ((hs).trans hk)
      dd ee h2 al ar k hk hs)

local notation "TOpposite" => arithmeticTargetPairOppositeOpen node data m k hk i j hi hj hij hsum
local notation "VOpposite" => olderUnequalOpen hπ data k hk (i + 1) (j + 1)
  (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1)
local notation "OOpposite" => unequalDepthDomain hπ di dj hkl data ((hdiff).trans hk) al ar

/-- The complete opposite domains agree in the original smooth arithmetic pair. -/
theorem arithmeticTargetSmoothOppositeOpen_eq :
    inc ⁻¹ᵁ TOpposite = P ⁻¹ᵁ VOpposite := by
  simpa only [arithmeticTargetPairOppositeOpen,
    successiveTensorPairOppositeOpen, olderUnequalOpen, atlasPairUnequalOpen,
    olderUnequalFormulaInput, Scheme.Hom.comp_preimage] using
    SchemeRestrictedOutputComparison.domain_eq (inc ≫ (E).hom) P input F
    (by simpa only [Category.assoc] using H) OOpposite

/-- The constructed opposite outputs agree as morphisms into the same smooth model. -/
theorem arithmeticTargetSmoothOppositeAddition_eq :
    (pullback fa fb : Scheme).homOfLE
        (arithmeticTargetSmoothOppositeOpen_eq node data m k hk i j hi hj hij hsum).le ≫
      (P ∣_ VOpposite) ≫ olderUnequalAddition hπ data k hk (i + 1) (j + 1)
        (Nat.lt_of_succ_le hi) (Nat.lt_of_succ_le hj) (Nat.add_le_add_right hij 1)
      =
        (inc ∣_ TOpposite) ≫ arithmeticTargetPairOppositeAddition
      node data m k hk i j hi hj hij hsum := by
  simpa only [olderUnequalAddition, atlasPairUnequalAddition,
    olderUnequalOpen, atlasPairUnequalOpen, arithmeticTargetPairOppositeOpen,
    successiveTensorPairOppositeOpen, Scheme.Hom.comp_preimage,
    arithmeticTargetPairOppositeAddition, successiveTensorPairOppositeAddition,
    olderUnequalFormulaInput, morphismRestrict_comp, Category.assoc] using
    SchemeRestrictedOutputComparison.output_eq (inc ≫ (E).hom) P input F
      (by simpa only [Category.assoc] using H) OOpposite
      (unequalDepthResolvedAddition hπ di dj hkl data ((hdiff).trans hk) al ar k hk hdiff)

end FLT.Mazur.WeierstrassDividedDepth
