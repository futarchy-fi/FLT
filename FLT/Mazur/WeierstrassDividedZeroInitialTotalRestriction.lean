/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatio
public import FLT.Mazur.WeierstrassDividedZeroDiagonalOpenRestriction

/-!
# Quotient squares for the complete initial open and node transports

Every accumulated factor preserves the original coefficient restriction.
The diagonal square allows the finite correction count to vary with the order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ρ" => arithmeticFullInitialNodeQuotient R π m W (π ^ 1)
local notation "N" => closingNormalizedRestriction data H m

/-- The first actual initial open comparison preserves the original full quotient map. -/
@[reassoc] theorem arithmeticZeroFirstAtlasIso_initial_restriction (b : Bool) :
    (arithmeticZeroFirstAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroFirstInitialRestriction hπ data H 0 hj u hu m b =
        ρ ≫ (arithmeticZeroFirstAtlasIso hπ data H (m + 1) hj u hu (.initial b)).hom := by
  rw [arithmeticZeroFirstAtlasIso_initial, arithmeticZeroFirstAtlasIso_initial]
  exact arithmeticZeroFirstInitialIso_restriction hπ data H 0 hj u hu m b

/-- The complete second initial open comparison retains its original quotient square. -/
@[reassoc] theorem arithmeticZeroSecondAtlasIso_initial_restriction (b : Bool) :
    (arithmeticZeroSecondAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroSecondInitialRestriction hπ data H 0 hj u hu m b =
        ρ ≫ (arithmeticZeroSecondAtlasIso hπ data H (m + 1) hj u hu (.initial b)).hom := by
  simp only [arithmeticZeroSecondAtlasIso, arithmeticZeroSecondAtlasCorrection,
    Iso.trans_hom, Category.assoc, arithmeticZeroSecondInitialIso_restriction]
  rw [← Category.assoc, arithmeticZeroFirstAtlasIso_initial_restriction, Category.assoc]

omit [IsBezout R] in
/-- Both actual second smoothings appear in the complete accumulated node square. -/
@[reassoc] theorem arithmeticZeroSecondInitialTotalNodeIso_restriction (b : Bool) :
    N ≫ (arithmeticZeroSecondInitialTotalNodeIso hπ data H (m + 1) hj u hu b).hom =
      (arithmeticZeroSecondInitialTotalNodeIso hπ data H m hj u hu b).hom ≫
        arithmeticZeroSecondInitialNodeRestriction hπ data H 0 hj u hu m b := by
  simp only [arithmeticZeroSecondInitialTotalNodeIso, Iso.trans_hom, ← Category.assoc]
  rw [arithmeticZeroFirstInitialNodeIso_restriction,
    Category.assoc, arithmeticZeroSecondInitialNodeIso_restriction, ← Category.assoc]

/-- The complete third initial open comparison retains its original quotient square. -/
@[reassoc] theorem arithmeticZeroThirdAtlasIso_initial_restriction (b : Bool) :
    (arithmeticZeroThirdAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroThirdInitialRestriction hπ data H 0 hj u hu m b =
        ρ ≫ (arithmeticZeroThirdAtlasIso hπ data H (m + 1) hj u hu (.initial b)).hom := by
  simp only [arithmeticZeroThirdAtlasIso, arithmeticZeroThirdAtlasCorrection,
    Iso.trans_hom, Category.assoc, arithmeticZeroThirdInitialIso_restriction]
  rw [← Category.assoc, arithmeticZeroSecondAtlasIso_initial_restriction, Category.assoc]

omit [IsBezout R] in
/-- Both actual third smoothings appear in the complete accumulated node square. -/
@[reassoc] theorem arithmeticZeroThirdInitialTotalNodeIso_restriction (b : Bool) :
    N ≫ (arithmeticZeroThirdInitialTotalNodeIso hπ data H (m + 1) hj u hu b).hom =
      (arithmeticZeroThirdInitialTotalNodeIso hπ data H m hj u hu b).hom ≫
        arithmeticZeroThirdInitialNodeRestriction hπ data H 0 hj u hu m b := by
  simp only [arithmeticZeroThirdInitialTotalNodeIso, Iso.trans_hom, ← Category.assoc]
  rw [arithmeticZeroSecondInitialTotalNodeIso_restriction,
    Category.assoc, arithmeticZeroThirdInitialNodeIso_restriction, ← Category.assoc]

/-- The complete fourth initial open comparison retains its original quotient square. -/
@[reassoc] theorem arithmeticZeroFourthAtlasIso_initial_restriction (b : Bool) :
    (arithmeticZeroFourthAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroFourthInitialRestriction hπ data H 0 hj u hu m b =
        ρ ≫ (arithmeticZeroFourthAtlasIso hπ data H (m + 1) hj u hu (.initial b)).hom := by
  simp only [arithmeticZeroFourthAtlasIso, arithmeticZeroFourthAtlasCorrection,
    Iso.trans_hom, Category.assoc, arithmeticZeroFourthInitialIso_restriction]
  rw [← Category.assoc, arithmeticZeroThirdAtlasIso_initial_restriction, Category.assoc]

omit [IsBezout R] in
/-- Both actual fourth smoothings appear in the complete accumulated node square. -/
@[reassoc] theorem arithmeticZeroFourthInitialTotalNodeIso_restriction (b : Bool) :
    N ≫ (arithmeticZeroFourthInitialTotalNodeIso hπ data H (m + 1) hj u hu b).hom =
      (arithmeticZeroFourthInitialTotalNodeIso hπ data H m hj u hu b).hom ≫
        arithmeticZeroFourthInitialNodeRestriction hπ data H 0 hj u hu m b := by
  simp only [arithmeticZeroFourthInitialTotalNodeIso, Iso.trans_hom, ← Category.assoc]
  rw [arithmeticZeroThirdInitialTotalNodeIso_restriction,
    Category.assoc, arithmeticZeroFourthInitialNodeIso_restriction, ← Category.assoc]

/-- The complete fifth initial open comparison retains its original quotient square. -/
@[reassoc] theorem arithmeticZeroFifthAtlasIso_initial_restriction (b : Bool) :
    (arithmeticZeroFifthAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroFifthInitialRestriction hπ data H 0 hj u hu m b =
        ρ ≫ (arithmeticZeroFifthAtlasIso hπ data H (m + 1) hj u hu (.initial b)).hom := by
  simp only [arithmeticZeroFifthAtlasIso, arithmeticZeroFifthAtlasCorrection,
    Iso.trans_hom, Category.assoc, arithmeticZeroFifthInitialIso_restriction]
  rw [← Category.assoc, arithmeticZeroFourthAtlasIso_initial_restriction, Category.assoc]

omit [IsBezout R] in
/-- Both actual fifth smoothings appear in the complete accumulated node square. -/
@[reassoc] theorem arithmeticZeroFifthInitialTotalNodeIso_restriction (b : Bool) :
    N ≫ (arithmeticZeroFifthInitialTotalNodeIso hπ data H (m + 1) hj u hu b).hom =
      (arithmeticZeroFifthInitialTotalNodeIso hπ data H m hj u hu b).hom ≫
        arithmeticZeroFifthInitialNodeRestriction hπ data H 0 hj u hu m b := by
  simp only [arithmeticZeroFifthInitialTotalNodeIso, Iso.trans_hom, ← Category.assoc]
  rw [arithmeticZeroFourthInitialTotalNodeIso_restriction,
    Category.assoc, arithmeticZeroFifthInitialNodeIso_restriction, ← Category.assoc]

/-- The full diagonal source open retains the original coefficient quotient. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialOpenIso_restriction (b : Bool) :
    (arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu b).hom ≫
      arithmeticZeroDiagonalInitialRestriction hπ data H 0 hj u hu m b =
        ρ ≫ (arithmeticZeroDiagonalInitialOpenIso hπ data H (m + 1) hj u hu b).hom := by
  simp only [arithmeticZeroDiagonalInitialOpenIso, arithmeticZeroFiniteAtlasIso,
    arithmeticZeroFiniteAtlasCorrection, Iso.trans_hom, Category.assoc,
    arithmeticZeroDiagonalInitialIso_restriction]
  rw [← Category.assoc, arithmeticZeroFifthAtlasIso_initial_restriction, Category.assoc]

omit [IsBezout R] in
/-- The whole diagonal node square uses the actual varying correction count and smoothing. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialTotalNodeIso_restriction (b : Bool) :
    N ≫ (arithmeticZeroDiagonalInitialTotalNodeIso hπ data H (m + 1) hj u hu b).hom =
      (arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu b).hom ≫
        arithmeticZeroDiagonalInitialNodeRestriction hπ data H 0 hj u hu m b := by
  simp only [arithmeticZeroDiagonalInitialTotalNodeIso, arithmeticZeroFiniteInitialTotalNodeIso,
    Iso.trans_hom, nodeParameterIso, eqToIso_refl, Iso.refl_hom, Category.comp_id,
    ← Category.assoc]
  rw [arithmeticZeroFifthInitialTotalNodeIso_restriction,
    Category.assoc, arithmeticZeroDiagonalInitialNodeIso_restriction, ← Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
