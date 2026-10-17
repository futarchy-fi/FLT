/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEndInputRestriction
public import FLT.Mazur.WeierstrassDividedFifthDeepAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthDeepNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowJointNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowTerminalGeometry

/-!
# Actual coefficient quotients at the fifth deep endpoints

The last, terminal and earlier installed arrows agree with their full concrete
coefficient maps. Initial and infinity arrows retain their fourth quotients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthDeepAtlasCorrection arithmeticFifthDeepEarlierIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (hj₄ : 4 ≤ j) (m : ℕ)
local notation "S" => arithmeticFifthDeepAtlasRestriction hπ data H j hj u hu hj₄
local notation "ρ" => closingNormalizedRestriction data H m
local notation "N" => fun k ↦ arithmeticFifthDeepLastIdentification hπ data H k j hj u hu
local notation "D" => fun k ↦ arithmeticFourthOuterLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFifthShallowLastOrientedIso hπ data H k j hj u hu

omit [IsBezout R] in
/-- The installed last label retains its full normalized coefficient quotient. -/
@[reassoc] theorem arithmeticFifthDeepLastIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) = ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticFifthDeepAtlasCorrection_restriction hπ data H j hj u hu hj₄ m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFifthDeepAtlasCorrection_last, arithmeticFifthDeepAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (D m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticFifthDeepLastInput_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFifthShallowLastOrientedIso_restriction_assoc]
  exact hh

omit [IsBezout R] in
/-- The installed terminal has the exact full fifth smoothing's coefficient map. -/
theorem arithmeticFifthDeepAtlasRestriction_terminal :
    S m .terminal = arithmeticFifthShallowTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (arithmeticFifthShallowTerminalIso hπ data H m j hj u hu).hom).mp
  simp only [arithmeticFifthDeepAtlasRestriction, arithmeticFifthDeepAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFifthDeepTerminalInput_restriction]
  exact arithmeticFifthShallowTerminalIso_restriction hπ data H j hj u hu m

omit [IsBezout R] in
/-- The whole initial open retains the same original fourth coefficient quotient. -/
theorem arithmeticFifthDeepAtlasRestriction_initial (b : Bool) :
    S m (.initial b) =
      arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu m (.initial b) := by
  simp only [arithmeticFifthDeepAtlasRestriction, arithmeticFifthDeepAtlasCorrection,
    Iso.refl_inv, Iso.refl_hom, Category.comp_id]
  exact Category.id_comp _

omit [IsBezout R] in
/-- Infinity retains its entire original fourth coefficient quotient. -/
theorem arithmeticFifthDeepAtlasRestriction_infinity :
    S m .infinity = arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu m .infinity := by
  simp only [arithmeticFifthDeepAtlasRestriction, arithmeticFifthDeepAtlasCorrection,
    Iso.refl_inv, Iso.refl_hom, Category.comp_id]
  exact Category.id_comp _

variable (a : ℕ) (ha : a + 4 = j)
local notation "M" => fun k ↦ arithmeticFifthDeepEarlierIdentification hπ data H k j hj u hu a ha
local notation "B" => fun k ↦
  arithmeticFifthDeepEarlierInputIdentification hπ data H k j hj u hu a ha
local notation "F" => fun k ↦ arithmeticFifthDeepEarlierIso hπ data H j hj u hu k
local notation "O" => fun k ↦ twistedRetainedOrientation data H k

omit [IsBezout R] in
/-- The installed earlier label has its changed fifth quotient and original orientation. -/
@[reassoc] theorem arithmeticFifthDeepEarlierIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticFifthDeepEarlierRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticFifthDeepAtlasCorrection_restriction hπ data H j hj u hu hj₄ m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFifthDeepAtlasCorrection_earlier hπ data H m j hj u hu hj₄ a ha b,
    arithmeticFifthDeepAtlasCorrection_earlier hπ data H (m + 1) j hj u hu hj₄ a ha b] at h
  have hh := congrArg (fun f ↦ (O m b).hom ≫ (B m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticFifthDeepEarlierInput_restriction_assoc, Iso.hom_inv_id_assoc,
    ← twistedRetainedOrientation_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (F m b).hom).mp
  rw [← arithmeticFifthDeepEarlierIso_restriction_assoc]
  exact hh

end FLT.Mazur.WeierstrassDividedDepth
