/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstAtlasSystem
public import FLT.Mazur.WeierstrassDividedZeroFirstOpenRestriction
public import FLT.Mazur.WeierstrassDividedFourthZeroRestriction

/-!
# Concrete coefficient maps in the first depth-zero atlas

The last node has its new smoothing quotient. The initial label uses the
quotient of the pulled-back original open; the common terminal keeps its
fourth smoothing quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFirstInitialIso arithmeticZeroFirstLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "S" => arithmeticZeroFirstAtlasRestriction hπ data H hj u hu
local notation "I" => fun k ↦ arithmeticZeroFirstInitialIso hπ data H k 0 hj u hu
local notation "J" => fun k ↦
  arithmeticFourthOuterInitialZeroIdentification hπ data H k 0 hj u hu rfl
local notation "N" => fun k ↦ arithmeticFourthOuterLastIdentification hπ data H k 0 hj u hu
local notation "O" => fun k ↦ twistedRetainedOrientation data H k
local notation "L" => fun k ↦ arithmeticZeroFirstLastIso hπ data H k 0 hj u hu

/-- The installed initial arrow is the quotient of the original full open. -/
theorem arithmeticZeroFirstAtlasRestriction_initial (b : Bool) :
    S m (.initial b) = arithmeticZeroFirstInitialRestriction hπ data H 0 hj u hu m b := by
  apply (cancel_epi (I m b).hom).mp
  rw [arithmeticZeroFirstInitialIso_restriction]
  have h := arithmeticZeroFirstAtlasCorrection_restriction hπ data H hj u hu m (.initial b)
  change ((J m b).inv ≫ (I m b).hom) ≫ S m (.initial b) =
    _ ≫ (J (m + 1) b).inv ≫ (I (m + 1) b).hom at h
  have hh := congrArg (fun f ↦ (J m b).hom ≫ f) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [← Category.assoc, arithmeticFourthZeroInitialInput_restriction,
    Category.assoc, Iso.hom_inv_id_assoc] at hh
  exact hh

omit [IsBezout R] in
/-- The unique last label uses the coefficient map of its actual changed smoothing. -/
theorem arithmeticZeroFirstAtlasRestriction_last (b : Bool) :
    S m (.retained ⟨0, by omega⟩ b) =
      arithmeticZeroFirstLastRestriction hπ data H 0 hj u hu m b := by
  apply (cancel_epi (L m b).hom).mp
  rw [← arithmeticZeroFirstLastIso_restriction]
  have h := arithmeticZeroFirstAtlasCorrection_restriction hπ data H hj u hu m
    (.retained ⟨0, by omega⟩ b)
  change ((N m b).inv ≫ (O m b).inv ≫ (L m b).hom) ≫ _ =
    _ ≫ (N (m + 1) b).inv ≫ (O (m + 1) b).inv ≫ (L (m + 1) b).hom at h
  have hh := congrArg (fun f ↦ (O m b).hom ≫ (N m b).hom ≫ f) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticFifthDeepLastInput_restriction_assoc, Iso.hom_inv_id_assoc,
    ← twistedRetainedOrientation_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  exact hh

omit [IsBezout R] in
/-- Both closing branches retain the same terminal's full fourth quotient. -/
theorem arithmeticZeroFirstAtlasRestriction_terminal :
    S m .terminal = arithmeticFourthTerminalRestriction hπ data H 0 hj u hu m := by
  simpa only [arithmeticZeroFirstAtlasRestriction, arithmeticZeroFirstAtlasCorrection,
    arithmeticZeroFirstAtlasObject, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using
    arithmeticFifthDeepTerminalInput_restriction hπ data H 0 hj u hu m

omit [IsBezout R] in
/-- Infinity keeps its complete original fourth-atlas quotient. -/
theorem arithmeticZeroFirstAtlasRestriction_infinity :
    S m .infinity = arithmeticFourthOuterAtlasRestriction hπ data H 0 hj u hu m .infinity := by
  simp only [arithmeticZeroFirstAtlasRestriction, arithmeticZeroFirstAtlasCorrection,
    arithmeticZeroFirstAtlasObject, Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

omit [IsBezout R] in
/-- Infinity is the original tensor coefficient map, after every correction round. -/
theorem arithmeticZeroFirstAtlasRestriction_infinity_coefficient :
    S m .infinity = arithmeticLabeledAtlasRestriction hπ data H m 1 hj .infinity := by
  rw [arithmeticZeroFirstAtlasRestriction_infinity]
  simp only [arithmeticFourthOuterAtlasRestriction, arithmeticFourthOuterAtlasCorrection,
    arithmeticFourthInitialAtlasCorrection, arithmeticFourthAtlasCorrection,
    arithmeticThirdInitialAtlasRestriction, arithmeticThirdInitialAtlasCorrection,
    arithmeticThirdAtlasRestriction, arithmeticThirdAtlasCorrection,
    arithmeticSecondJointAtlasRestriction, arithmeticSecondJointAtlasCorrection,
    arithmeticResidualLiftAtlasRestriction, arithmeticResidualLiftAtlasCorrection,
    changedArithmeticAtlasRestriction, twistedArithmeticAtlasRestriction,
    arithmeticFourthOuterAtlasObject, arithmeticFourthInitialAtlasObject,
    arithmeticFourthAtlasObject, arithmeticThirdInitialAtlasObject, arithmeticThirdAtlasObject,
    arithmeticSecondJointAtlasObject, arithmeticResidualLiftAtlasObject,
    changedArithmeticAtlasObject, twistedArithmeticAtlasObject,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
