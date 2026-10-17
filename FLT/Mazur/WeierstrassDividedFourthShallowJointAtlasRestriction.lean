/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasSystem
public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasIncoming
public import FLT.Mazur.WeierstrassDividedFourthNodeRestriction
public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry
public import FLT.Mazur.WeierstrassDividedThirdAtlasNodeRestriction

public import FLT.Mazur.WeierstrassDividedFourthAtlasNodeRestriction

/-!
# Complete coefficient maps for the fourth depth-two interior charts

The last, predecessor and terminal comparisons retain the original arithmetic
quotient. These squares supply the old side of the fifth atlas restrictions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthShallowAtlasCorrection arithmeticFourthLastOrientedIso
  arithmeticFourthPrecedingIso arithmeticFourthShallowAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticFourthShallowAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticFourthShallowLastIdentification hπ data H k j hj u hu
local notation "N₂" => fun k ↦ arithmeticThirdLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthLastOrientedIso hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

local notation "E" => fun k ↦ arithmeticFourthShallowAtlasCorrection hπ data H k j hj u hu

/-- The last correction retains the original full factor from the third atlas. -/
theorem arithmeticFourthShallowAtlasCorrection_last (b : Bool) :
    arithmeticFourthShallowAtlasCorrection hπ data H m j hj u hu (.retained ⟨j, by omega⟩ b) =
      (N₂ m b).symm ≪≫ C m b ≪≫ N m b := by
  apply Iso.ext
  apply (cancel_mono
    (arithmeticFourthShallowAtlasChart hπ data H m j hj u hu (.retained ⟨j, by omega⟩ b))).mp
  rw [arithmeticFourthShallowAtlasCorrection_chart]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    arithmeticFourthShallowLast_chart, Iso.inv_hom_id_assoc]

/-- The installed last label has exactly the full original coefficient restriction. -/
@[reassoc] theorem arithmeticFourthShallowLastIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) = ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthShallowAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthShallowAtlasCorrection_last hπ data H j hj u hu m b,
    arithmeticFourthShallowAtlasCorrection_last hπ data H j hj u hu (m + 1) b] at h
  have hh := congrArg (fun f ↦ (N₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdLastIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthLastOrientedIso_restriction_assoc]
  exact hh

variable (a : ℕ) (ha : a + 1 = j) (hj₂ : 2 ≤ j)
local notation "M" => fun k ↦
  arithmeticFourthShallowPrecedingIdentification hπ data H k j hj u hu a ha hj₂
local notation "M₂" => fun k ↦
  arithmeticThirdPrecedingIdentification hπ data H k j hj u hu a ha
local notation "P" => fun k ↦ arithmeticFourthPrecedingIso hπ data H k j hj u hu

omit [IsBezout R] in
/-- The installed predecessor's restriction retains its exact fourth smoothing. -/
@[reassoc] theorem arithmeticFourthShallowPrecedingIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticFourthPrecedingRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticFourthShallowAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthShallowAtlasCorrection_preceding hπ data H m j hj u hu a ha hj₂ b,
    arithmeticFourthShallowAtlasCorrection_preceding hπ data H (m + 1) j hj u hu a ha hj₂ b] at h
  have hh := congrArg (fun f ↦ (M₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdPrecedingIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (P m b).hom).mp
  rw [← arithmeticFourthPrecedingIso_restriction_assoc]
  exact hh

omit [IsBezout R] in
/-- The untouched terminal keeps its full fourth coefficient map. -/
theorem arithmeticFourthShallowAtlasRestriction_terminal :
    S m .terminal = arithmeticFourthTerminalRestriction hπ data H j hj u hu m := by
  simp only [arithmeticFourthShallowAtlasRestriction, arithmeticFourthShallowAtlasCorrection,
    arithmeticFourthOuterAtlasCorrection, arithmeticFourthInitialAtlasCorrection]
  change arithmeticFourthAtlasRestriction hπ data H j hj u hu m .terminal = _
  exact arithmeticFourthAtlasRestriction_terminal hπ data H j hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
