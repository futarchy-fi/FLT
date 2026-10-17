/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdAtlasNodeRestriction
public import FLT.Mazur.WeierstrassDividedThirdEarlierGeometry

/-!
# Coefficient restriction at the installed earlier third node

The earlier label has the coefficient map of its full changed smoothing.
Its comparison starts at the unchanged second-atlas coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdAtlasCorrection arithmeticThirdEarlierOrientedIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "S₂" => arithmeticSecondJointAtlasRestriction hπ data H j hj u hu
local notation "N₂" => fun k ↦ arithmeticSecondJointEarlierIdentification hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

/-- The earlier second-atlas identification preserves the original coefficient restriction. -/
@[reassoc] theorem arithmeticSecondJointEarlierIdentification_restriction
    (i : Fin (j + 1)) (hi : i.val + 1 < j) (b : Bool) :
    (N₂ m i hi b).hom ≫ S₂ m (.retained i b) = ρ ≫ (N₂ (m + 1) i hi b).hom := by
  exact arithmeticSecondJointUnchangedIdentification_restriction
    hπ data H j hj u hu m i (by omega) (by omega) b

variable (a : ℕ) (ha : a + 2 = j)
local notation "S" => arithmeticThirdAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticThirdEarlierIdentification hπ data H k j hj u hu a ha
local notation "C" => fun k ↦ arithmeticThirdEarlierOrientedIso hπ data H k j hj u hu

/-- The installed earlier node retains its exact third-smoothing coefficient map. -/
@[reassoc] theorem arithmeticThirdEarlierIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticThirdEarlierRestriction hπ data H j hj u hu m b ≫ (N (m + 1) b).hom := by
  have h := arithmeticThirdAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticThirdAtlasCorrection_earlier hπ data H m j hj u hu a ha b,
    arithmeticThirdAtlasCorrection_earlier hπ data H (m + 1) j hj u hu a ha b] at h
  have hh := congrArg
    (fun f ↦ (N₂ m ⟨a, by omega⟩ (show a + 1 < j by omega) b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticSecondJointEarlierIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticThirdEarlierOrientedIso_restriction_assoc]
  exact hh

end FLT.Mazur.WeierstrassDividedDepth
