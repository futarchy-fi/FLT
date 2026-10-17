/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEndInputRestriction
public import FLT.Mazur.WeierstrassDividedFifthFartherEndIdentification
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthDeepNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowJointNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowTerminalGeometry

/-!
# Actual coefficient quotients at the depth-three fifth endpoints

The last and terminal installed arrows agree with their full concrete
coefficient maps. Infinity retains its fourth quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthFartherAtlasCorrection arithmeticFifthDeepEarlierIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (ha₃ : 3 = j) (m : ℕ)
local notation "S" => arithmeticFifthFartherAtlasRestriction hπ data H j hj u hu ha₃
local notation "ρ" => closingNormalizedRestriction data H m
local notation "N" => fun k ↦ arithmeticFifthFartherLastIdentification hπ data H k j hj u hu
local notation "D" => fun k ↦ arithmeticFourthOuterLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFifthShallowLastOrientedIso hπ data H k j hj u hu

omit [IsBezout R] in
/-- The installed last label retains its full normalized coefficient quotient. -/
@[reassoc] theorem arithmeticFifthFartherLastIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) = ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticFifthFartherAtlasCorrection_restriction hπ data H j hj u hu ha₃ m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFifthFartherAtlasCorrection_last, arithmeticFifthFartherAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (D m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticFifthDeepLastInput_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFifthShallowLastOrientedIso_restriction_assoc]
  exact hh

omit [IsBezout R] in
/-- The installed terminal has the exact full fifth smoothing's coefficient map. -/
theorem arithmeticFifthFartherAtlasRestriction_terminal :
    S m .terminal = arithmeticFifthShallowTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (arithmeticFifthShallowTerminalIso hπ data H m j hj u hu).hom).mp
  simp only [arithmeticFifthFartherAtlasRestriction, arithmeticFifthFartherAtlasCorrection,
    Iso.hom_inv_id_assoc]
  rw [arithmeticFifthDeepTerminalInput_restriction]
  exact arithmeticFifthShallowTerminalIso_restriction hπ data H j hj u hu m

omit [IsBezout R] in
/-- Infinity retains its entire original fourth coefficient quotient. -/
theorem arithmeticFifthFartherAtlasRestriction_infinity :
    S m .infinity = arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu m .infinity := by
  simp only [arithmeticFifthFartherAtlasRestriction, arithmeticFifthFartherAtlasCorrection,
    Iso.refl_inv, Iso.refl_hom, Category.comp_id]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
