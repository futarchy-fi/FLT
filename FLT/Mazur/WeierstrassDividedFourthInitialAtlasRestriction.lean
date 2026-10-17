/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasSystem
public import FLT.Mazur.WeierstrassDividedFourthInitialLast
public import FLT.Mazur.WeierstrassDividedFourthInitialOpenRestriction
public import FLT.Mazur.WeierstrassDividedFourthAtlasNodeRestriction
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasRestriction
public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry
public import FLT.Mazur.WeierstrassDividedThirdAtlasNodeRestriction

/-!
# Explicit coefficient maps in the installed fourth initial atlas

The transported restrictions on the last node, its predecessor and the
initial open are their actual coefficient maps, including all smoothing drifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthInitialAtlasCorrection arithmeticFourthLastOrientedIso
  arithmeticFourthInitialNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticFourthInitialAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticFourthInitialLastIdentification hπ data H k j hj u hu
local notation "N₂" => fun k ↦ arithmeticThirdLastIdentification hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthLastOrientedIso hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

/-- The installed last label has exactly the full original coefficient restriction. -/
@[reassoc] theorem arithmeticFourthInitialLastIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨j, by omega⟩ b) = ρ ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthInitialAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨j, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthInitialAtlasCorrection_last, arithmeticFourthInitialAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (N₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdLastIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthLastOrientedIso_restriction_assoc]
  exact hh

variable (ha : 1 = j)
local notation "M" => fun k ↦ arithmeticFourthInitialNeighborIdentification hπ data H k j hj u hu ha
local notation "M₂" => fun k ↦
  arithmeticThirdPrecedingIdentification hπ data H k j hj u hu 0 ha
local notation "P" => fun k ↦ arithmeticFourthInitialNeighborIso hπ data H k j hj u hu

/-- The installed predecessor's restriction retains its exact fourth smoothing. -/
@[reassoc] theorem arithmeticFourthInitialNeighborIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨0, by omega⟩ b) =
      arithmeticFourthInitialNeighborRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticFourthInitialAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨0, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthInitialAtlasCorrection_neighbor hπ data H m j hj u hu ha b,
    arithmeticFourthInitialAtlasCorrection_neighbor hπ data H (m + 1) j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (M₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdPrecedingIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (P m b).hom).mp
  rw [← arithmeticFourthInitialNeighborIso_restriction_assoc]
  exact hh

local notation "J" => fun k ↦ arithmeticFourthInitialIdentification hπ data H k j hj u hu ha
local notation "J₃" => fun k ↦ arithmeticThirdInitialIdentification hπ data H k j hj u hu ha
local notation "I" => fun k ↦ arithmeticFourthInitialIso hπ data H k j hj u hu

/-- The installed full initial open uses its actual transported coefficient quotient. -/
@[reassoc] theorem arithmeticFourthInitialIdentification_restriction (b : Bool) :
    (J m b).hom ≫ S m (.initial b) =
      arithmeticFourthInitialOpenRestriction hπ data H j hj u hu m b ≫ (J (m + 1) b).hom := by
  have h := arithmeticFourthInitialAtlasCorrection_restriction
    hπ data H j hj u hu m (.initial b)
  dsimp only at h
  rw [arithmeticFourthInitialAtlasCorrection_initial hπ data H m j hj u hu ha b,
    arithmeticFourthInitialAtlasCorrection_initial hπ data H (m + 1) j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (J₃ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (I m b).hom).mp
  rw [arithmeticFourthInitialIso_restriction_assoc]
  exact hh

end FLT.Mazur.WeierstrassDividedDepth
