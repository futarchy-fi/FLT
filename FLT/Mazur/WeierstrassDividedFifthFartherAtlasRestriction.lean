/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthFartherIdentification
public import FLT.Mazur.WeierstrassDividedFifthFartherOpenRestriction
public import FLT.Mazur.WeierstrassDividedFifthFartherInputRestriction

/-!
# Explicit coefficient maps in the installed fifth depth-three initial atlas

The initial open and its earlier retained neighbor use their actual
coefficient maps, including all fifth-order smoothing drifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthFartherAtlasCorrection arithmeticFourthLastOrientedIso
  arithmeticFifthFartherNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
variable (ha : 3 = j)
local notation "S" => arithmeticFifthFartherAtlasRestriction hπ data H j hj u hu ha
local notation "M" => fun k ↦ arithmeticFifthFartherNeighborIdentification hπ data H k j hj u hu ha
local notation "M₂" => fun k ↦
  arithmeticFourthFartherIdentification hπ data H k j hj u hu 0 ha
local notation "P" => fun k ↦ arithmeticFifthFartherNeighborIso hπ data H k j hj u hu

omit [IsBezout R] in
/-- The installed earlier neighbor's restriction retains its exact fifth smoothing. -/
@[reassoc] theorem arithmeticFifthFartherNeighborIdentification_restriction (b : Bool) :
    (M m b).hom ≫ S m (.retained ⟨0, by omega⟩ b) =
      arithmeticFifthFartherNeighborRestriction hπ data H j hj u hu m b ≫ (M (m + 1) b).hom := by
  have h := arithmeticFifthFartherAtlasCorrection_restriction hπ data H j hj u hu ha m
    (.retained ⟨0, by omega⟩ b)
  dsimp only at h
  rw [arithmeticFifthFartherAtlasCorrection_neighbor hπ data H m j hj u hu ha b,
    arithmeticFifthFartherAtlasCorrection_neighbor hπ data H (m + 1) j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (M₂ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticFourthFartherIdentification_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (P m b).hom).mp
  rw [← arithmeticFifthFartherNeighborIso_restriction_assoc]
  exact hh

local notation "J" => fun k ↦ arithmeticFifthFartherIdentification hπ data H k j hj u hu ha
local notation "J₃" => fun k ↦
  arithmeticFourthOuterInitialThreeIdentification hπ data H k j hj u hu ha
local notation "I" => fun k ↦ arithmeticFifthFartherIso hπ data H k j hj u hu

/-- The installed full initial open uses its actual transported coefficient quotient. -/
@[reassoc] theorem arithmeticFifthFartherIdentification_restriction (b : Bool) :
    (J m b).hom ≫ S m (.initial b) =
      arithmeticFifthFartherOpenRestriction hπ data H j hj u hu m b ≫ (J (m + 1) b).hom := by
  have h := arithmeticFifthFartherAtlasCorrection_restriction
    hπ data H j hj u hu ha m (.initial b)
  dsimp only at h
  rw [arithmeticFifthFartherAtlasCorrection_initial hπ data H m j hj u hu ha b,
    arithmeticFifthFartherAtlasCorrection_initial hπ data H (m + 1) j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (J₃ m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticFifthFartherInitialInput_restriction_assoc,
    Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (I m b).hom).mp
  rw [arithmeticFifthFartherIso_restriction_assoc]
  exact hh

end FLT.Mazur.WeierstrassDividedDepth
