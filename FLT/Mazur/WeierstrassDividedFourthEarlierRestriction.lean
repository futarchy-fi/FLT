/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthAtlasNodeRestriction
public import FLT.Mazur.WeierstrassDividedFourthEarlierGeometry
public import FLT.Mazur.WeierstrassDividedThirdEarlierRestriction

/-!
# Coefficient restriction at the installed earlier fourth node

The earlier label has the coefficient map of its full changed smoothing.
Its comparison starts at the full third-atlas coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthAtlasCorrection arithmeticFourthEarlierIso
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
variable (a : ℕ) (ha : a + 2 = j)
local notation "S" => arithmeticFourthAtlasRestriction hπ data H j hj u hu
local notation "N" => fun k ↦ arithmeticFourthEarlierIdentification hπ data H k j hj u hu a ha
local notation "N₃" => fun k ↦
  arithmeticThirdEarlierIdentification hπ data H k j hj u hu a ha
local notation "C" => fun k ↦ arithmeticFourthEarlierIso hπ data H k j hj u hu

/-- The installed earlier node retains its exact fourth-smoothing coefficient map. -/
@[reassoc] theorem arithmeticFourthEarlierIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨a, by omega⟩ b) =
      arithmeticFourthEarlierRestriction hπ data H j hj u hu m b ≫ (N (m + 1) b).hom := by
  have h := arithmeticFourthAtlasCorrection_restriction hπ data H j hj u hu m
    (.retained ⟨a, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFourthAtlasCorrection_earlier hπ data H m j hj u hu a ha b,
    arithmeticFourthAtlasCorrection_earlier hπ data H (m + 1) j hj u hu a ha b] at h
  have hh := congrArg
    (fun f ↦ (N₃ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticThirdInitialAtlasRestriction_retained,
    arithmeticThirdEarlierIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFourthEarlierIso_restriction_assoc]
  exact hh

end FLT.Mazur.WeierstrassDividedDepth
