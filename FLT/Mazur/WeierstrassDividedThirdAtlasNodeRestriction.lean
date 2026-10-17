/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdAtlasSystem
public import FLT.Mazur.WeierstrassDividedThirdAtlasIdentification
public import FLT.Mazur.WeierstrassDividedThirdNodeRestriction
public import FLT.Mazur.WeierstrassDividedThirdTerminalGeometry

/-!
# Explicit coefficient maps in the installed third atlas

The transported restrictions on the last node, its predecessor and the
terminal are their actual coefficient maps, including all smoothing drifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdAtlasCorrection arithmeticThirdLastOrientedIso arithmeticThirdPrecedingIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticThirdAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticThirdLastIdentification hπ data H k j hj u hu
local notation "N₂" => fun k ↦ arithmeticSecondJointLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticThirdLastOrientedIso hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

/-- The installed last label has exactly the full original coefficient restriction. -/
@[reassoc] theorem arithmeticThirdLastIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) = ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticThirdAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  rw [arithmeticThirdAtlasCorrection_last, arithmeticThirdAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (N₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticSecondJointLastIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticThirdLastOrientedIso_restriction_assoc]
  exact hh

variable (a : ℕ) (ha : a + 1 = j)
local notation "M" => fun k ↦ arithmeticThirdPrecedingIdentification hπ data H k j hj u hu a ha
local notation "M₂" => fun k ↦
  arithmeticSecondJointPrecedingIdentification hπ data H k j hj u hu a ha
local notation "P" => fun k ↦ arithmeticThirdPrecedingIso hπ data H k j hj u hu

/-- The installed predecessor's restriction retains its exact third smoothing. -/
@[reassoc] theorem arithmeticThirdPrecedingIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticThirdPrecedingRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticThirdAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticThirdAtlasCorrection_preceding hπ data H m j hj u hu a ha b,
    arithmeticThirdAtlasCorrection_preceding hπ data H (m + 1) j hj u hu a ha b] at h
  have hh := congrArg (fun f ↦ (M₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticSecondJointPrecedingIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (P m b).hom).mp
  rw [← arithmeticThirdPrecedingIso_restriction_assoc]
  exact hh

local notation "F" => fun k ↦ arithmeticThirdTerminalIso hπ data H k j hj u hu

/-- The actual terminal restriction is the coefficient map on its thrice-corrected smoothing. -/
theorem arithmeticThirdAtlasRestriction_terminal :
    S m .terminal = arithmeticThirdTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (F m).hom).mp
  have h := arithmeticThirdAtlasCorrection_restriction hπ data H j hj u hu m .terminal
  simp only [arithmeticThirdAtlasCorrection] at h
  change (F m).hom ≫ S m .terminal =
    arithmeticSecondJointAtlasRestriction hπ data H j hj u hu m .terminal ≫
      (F (m + 1)).hom at h
  rw [arithmeticSecondJointAtlasRestriction_terminal,
    arithmeticThirdTerminalIso_restriction] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
