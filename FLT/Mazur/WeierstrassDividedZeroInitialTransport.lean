/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasOverlaps
public import FLT.Mazur.PullbackOneLegTransport

/-!
# Full original initial punctures in the depth-zero finite atlas

Each correction carries the entire original initial puncture by a Laurent
isomorphism. The original Mobius parameter and every finite factor are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFirstInitialIso arithmeticZeroFirstAtlasChart
  arithmeticFourthOuterAtlasChart arithmeticThirdAtlasChart changedArithmeticAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialNormalizedPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The first full initial atlas comparison is the constructed pullback-open comparison. -/
theorem arithmeticZeroFirstAtlasIso_initial (b : Bool) :
    (arithmeticZeroFirstAtlasIso hπ data H m hj u hu (.initial b)).hom =
      (arithmeticZeroFirstInitialIso hπ data H m 0 hj u hu b).hom := by
  apply (cancel_mono
    (arithmeticZeroFirstAtlasChart hπ data H m hj u hu (.initial b))).mp
  rw [← arithmeticZeroFirstAtlasIso_chart, arithmeticZeroFirstInitial_chart,
    arithmeticFourthOuterAtlasChart_initial_zero, arithmeticThirdAtlasChart_initial]
  have h := changedArithmeticAtlasIso_chart hπ data H m 0 hj u hu (.initial b)
  change _ = (𝟙 _ ≫ 𝟙 _) ≫ _ at h
  simpa only [Category.id_comp] using h

/-- The first initial correction transports the original full Laurent puncture. -/
theorem arithmeticZeroFirstAtlasIso_initial_transport (b : Bool) :
    ∃ e : Spec (.of (Localization.Away (NodalFiber.p
      (algebraMap R Q (π ^ 1))))) ≅ branchTorus Q,
      P ≫ (arithmeticZeroFirstAtlasIso hπ data H m hj u hu (.initial b)).hom =
        e.hom ≫ arithmeticZeroFirstInitialPuncture hπ data H m 0 hj u hu b := by
  refine ⟨N ≪≫ punctureSpecIso (correctionPunctureFactor R π m τ
    (arithmeticZeroFirstInitialIntegralField hπ data H 0 hj u hu b) true), ?_⟩
  simp only [arithmeticZeroFirstAtlasIso_initial, arithmeticZeroFirstInitialPuncture,
    Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The second initial correction retains the entire original puncture. -/
theorem arithmeticZeroSecondAtlasIso_initial_transport (b : Bool) :
    ∃ e : Spec (.of (Localization.Away (NodalFiber.p
      (algebraMap R Q (π ^ 1))))) ≅ branchTorus Q,
      P ≫ (arithmeticZeroSecondAtlasIso hπ data H m hj u hu (.initial b)).hom =
        e.hom ≫ arithmeticZeroSecondInitialPuncture hπ data H m 0 hj u hu b := by
  obtain ⟨e, he⟩ := arithmeticZeroFirstAtlasIso_initial_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (correctionPunctureFactor R π m
    (arithmeticZeroFirstInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroSecondInitialIntegralField hπ data H 0 hj u hu b) true), ?_⟩
  simp only [arithmeticZeroSecondAtlasIso, arithmeticZeroSecondAtlasCorrection,
    arithmeticZeroSecondInitialPuncture, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc]

/-- The third initial correction retains the entire original puncture. -/
theorem arithmeticZeroThirdAtlasIso_initial_transport (b : Bool) :
    ∃ e : Spec (.of (Localization.Away (NodalFiber.p
      (algebraMap R Q (π ^ 1))))) ≅ branchTorus Q,
      P ≫ (arithmeticZeroThirdAtlasIso hπ data H m hj u hu (.initial b)).hom =
        e.hom ≫ arithmeticZeroThirdInitialPuncture hπ data H m 0 hj u hu b := by
  obtain ⟨e, he⟩ := arithmeticZeroSecondAtlasIso_initial_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (correctionPunctureFactor R π m
    (arithmeticZeroSecondInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroThirdInitialIntegralField hπ data H 0 hj u hu b) true), ?_⟩
  simp only [arithmeticZeroThirdAtlasIso, arithmeticZeroThirdAtlasCorrection,
    arithmeticZeroThirdInitialPuncture, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc]

/-- The fourth initial correction retains the entire original puncture. -/
theorem arithmeticZeroFourthAtlasIso_initial_transport (b : Bool) :
    ∃ e : Spec (.of (Localization.Away (NodalFiber.p
      (algebraMap R Q (π ^ 1))))) ≅ branchTorus Q,
      P ≫ (arithmeticZeroFourthAtlasIso hπ data H m hj u hu (.initial b)).hom =
        e.hom ≫ arithmeticZeroFourthInitialPuncture hπ data H m 0 hj u hu b := by
  obtain ⟨e, he⟩ := arithmeticZeroThirdAtlasIso_initial_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (correctionPunctureFactor R π m
    (arithmeticZeroThirdInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroFourthInitialIntegralField hπ data H 0 hj u hu b) true), ?_⟩
  simp only [arithmeticZeroFourthAtlasIso, arithmeticZeroFourthAtlasCorrection,
    arithmeticZeroFourthInitialPuncture, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc]

/-- The fifth initial correction retains the entire original puncture. -/
theorem arithmeticZeroFifthAtlasIso_initial_transport (b : Bool) :
    ∃ e : Spec (.of (Localization.Away (NodalFiber.p
      (algebraMap R Q (π ^ 1))))) ≅ branchTorus Q,
      P ≫ (arithmeticZeroFifthAtlasIso hπ data H m hj u hu (.initial b)).hom =
        e.hom ≫ arithmeticZeroFifthInitialPuncture hπ data H m 0 hj u hu b := by
  obtain ⟨e, he⟩ := arithmeticZeroFourthAtlasIso_initial_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (correctionPunctureFactor R π m
    (arithmeticZeroFourthInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroFifthInitialIntegralField hπ data H 0 hj u hu b) true), ?_⟩
  simp only [arithmeticZeroFifthAtlasIso, arithmeticZeroFifthAtlasCorrection,
    arithmeticZeroFifthInitialPuncture, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc]

/-- Every finite initial correction preserves the whole original Laurent boundary. -/
theorem arithmeticZeroFiniteAtlasIso_initial_transport (k : ℕ) (b : Bool) :
    ∃ e : Spec (.of (Localization.Away (NodalFiber.p
      (algebraMap R Q (π ^ 1))))) ≅ branchTorus Q,
      P ≫ (arithmeticZeroFiniteAtlasIso hπ data H k m hj u hu (.initial b)).hom =
        e.hom ≫ arithmeticZeroFiniteInitialPuncture hπ data H k m 0 hj u hu b := by
  obtain ⟨e, he⟩ := arithmeticZeroFifthAtlasIso_initial_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso
    (arithmeticZeroFiniteInitialPunctureEquiv hπ data H 0 hj u hu k m b true), ?_⟩
  simp only [arithmeticZeroFiniteAtlasIso, arithmeticZeroFiniteAtlasCorrection,
    arithmeticZeroFiniteInitialPuncture, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
