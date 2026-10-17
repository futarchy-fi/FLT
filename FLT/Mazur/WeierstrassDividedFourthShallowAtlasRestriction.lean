/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasSystem
public import FLT.Mazur.WeierstrassDividedFourthShallowIdentification
public import FLT.Mazur.WeierstrassDividedThirdEarlierRestriction
public import FLT.Mazur.WeierstrassDividedFourthShallowOpenRestriction
public import FLT.Mazur.WeierstrassDividedFourthAtlasNodeRestriction
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasRestriction
public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry
public import FLT.Mazur.WeierstrassDividedThirdAtlasNodeRestriction

/-!
# Explicit coefficient maps in the installed fourth initial atlas

The initial open and its earlier retained neighbor use their actual
coefficient maps, including all fourth-order smoothing drifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthShallowAtlasCorrection arithmeticFourthLastOrientedIso
  arithmeticFourthShallowNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S" => arithmeticFourthShallowAtlasRestriction hπ data H j hj u hu
variable (ha : 2 = j)
local notation "M" => fun k ↦ arithmeticFourthShallowNeighborIdentification hπ data H k j hj u hu ha
local notation "M₂" => fun k ↦
  arithmeticThirdEarlierIdentification hπ data H k j hj u hu 0 ha
local notation "P" => fun k ↦ arithmeticFourthShallowNeighborIso hπ data H k j hj u hu

/-- The installed earlier neighbor's restriction retains its exact fourth smoothing. -/
@[reassoc] theorem arithmeticFourthShallowNeighborIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨0, by omega⟩ b) =
      arithmeticFourthShallowNeighborRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticFourthShallowAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨0, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthShallowAtlasCorrection_neighbor hπ data H m j hj u hu ha b,
    arithmeticFourthShallowAtlasCorrection_neighbor hπ data H (m + 1) j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (M₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdEarlierIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (P m b).hom).mp
  rw [← arithmeticFourthShallowNeighborIso_restriction_assoc]
  exact hh

local notation "J" => fun k ↦ arithmeticFourthShallowIdentification hπ data H k j hj u hu ha
local notation "J₃" => fun k ↦ arithmeticThirdShallowInitialIdentification hπ data H k j hj u hu ha
local notation "I" => fun k ↦ arithmeticFourthShallowIso hπ data H k j hj u hu

/-- The installed full initial open uses its actual transported coefficient quotient. -/
@[reassoc] theorem arithmeticFourthShallowIdentification_restriction (b : Bool) :
    (J m b).hom ≫ S m (.initial b) =
      arithmeticFourthShallowOpenRestriction hπ data H j hj u hu m b ≫ (J (m + 1) b).hom := by
  have h := arithmeticFourthShallowAtlasCorrection_restriction
    hπ data H j hj u hu m (.initial b)
  dsimp only at h
  rw [arithmeticFourthShallowAtlasCorrection_initial hπ data H m j hj u hu ha b,
    arithmeticFourthShallowAtlasCorrection_initial hπ data H (m + 1) j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (J₃ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdShallowInitialIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (I m b).hom).mp
  rw [arithmeticFourthShallowIso_restriction_assoc]
  exact hh

end FLT.Mazur.WeierstrassDividedDepth
