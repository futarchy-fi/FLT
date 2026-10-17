/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthAtlasSystem
public import FLT.Mazur.WeierstrassDividedFourthAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFourthNodeRestriction
public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry
public import FLT.Mazur.WeierstrassDividedThirdAtlasNodeRestriction

/-!
# Explicit coefficient maps in the installed fourth atlas

The transported restrictions on the last node, its predecessor and the
terminal are their actual coefficient maps, including all smoothing drifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthAtlasCorrection arithmeticFourthLastOrientedIso arithmeticFourthPrecedingIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticFourthAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticFourthLastIdentification hπ data H k j hj u hu
local notation "N₂" => fun k ↦ arithmeticThirdLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthLastOrientedIso hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

/-- Retained labels keep their exact quotient under the depth-one initial correction. -/
theorem arithmeticThirdInitialAtlasRestriction_retained (a : Fin (j + 1)) (b : Bool) :
    arithmeticThirdInitialAtlasRestriction hπ data H j hj u hu m (.retained a b) =
      arithmeticThirdAtlasRestriction hπ data H j hj u hu m (.retained a b) := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- The depth-one initial correction preserves the complete terminal quotient. -/
theorem arithmeticThirdInitialAtlasRestriction_terminal :
    arithmeticThirdInitialAtlasRestriction hπ data H j hj u hu m .terminal =
      arithmeticThirdAtlasRestriction hπ data H j hj u hu m .terminal := by
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- The installed last label has exactly the full original coefficient restriction. -/
@[reassoc] theorem arithmeticFourthLastIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) = ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthAtlasCorrection_last, arithmeticFourthAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (N₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdLastIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthLastOrientedIso_restriction_assoc]
  exact hh

variable (a : ℕ) (ha : a + 1 = j)
local notation "M" => fun k ↦ arithmeticFourthPrecedingIdentification hπ data H k j hj u hu a ha
local notation "M₂" => fun k ↦
  arithmeticThirdPrecedingIdentification hπ data H k j hj u hu a ha
local notation "P" => fun k ↦ arithmeticFourthPrecedingIso hπ data H k j hj u hu

/-- The installed predecessor's restriction retains its exact fourth smoothing. -/
@[reassoc] theorem arithmeticFourthPrecedingIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticFourthPrecedingRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticFourthAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthAtlasCorrection_preceding hπ data H m j hj u hu a ha b,
    arithmeticFourthAtlasCorrection_preceding hπ data H (m + 1) j hj u hu a ha b] at h
  have hh := congrArg (fun f ↦ (M₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdPrecedingIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (P m b).hom).mp
  rw [← arithmeticFourthPrecedingIso_restriction_assoc]
  exact hh

local notation "F" => fun k ↦ arithmeticFourthTerminalIso hπ data H k j hj u hu

/-- The actual terminal restriction is the coefficient map on its four-times-corrected smoothing. -/
theorem arithmeticFourthAtlasRestriction_terminal :
    S m .terminal = arithmeticFourthTerminalRestriction hπ data H j hj u hu m := by
  apply (cancel_epi (F m).hom).mp
  have h := arithmeticFourthAtlasCorrection_restriction hπ data H j hj u hu m .terminal
  simp only [arithmeticFourthAtlasCorrection] at h
  change (F m).hom ≫ S m .terminal =
    arithmeticThirdInitialAtlasRestriction hπ data H j hj u hu m .terminal ≫
      (F (m + 1)).hom at h
  rw [arithmeticThirdInitialAtlasRestriction_terminal,
    arithmeticThirdAtlasRestriction_terminal] at h
  exact h.trans (arithmeticFourthTerminalIso_restriction hπ data H j hj u hu m)

end FLT.Mazur.WeierstrassDividedDepth
