/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialLastGeometry
public import FLT.Mazur.WeierstrassDividedFifthInitialResidualAlgebra
public import FLT.Mazur.WeierstrassDividedFourthTransitions

/-!
# Geometric transitions for the full fifth depth-one last node

Both last-node edges use the same complete fifth factor. Their algebraic
coordinate changes agree with the geometric ones.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => fun b ↦ twoBranchCorrectionPunctureFactor R π m τ
  (arithmeticFifthInitialLastIntegralField hπ data H j hj u hu b)
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticFifthInitialLastOrientedIso hπ data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m

/-- Express either retained puncture substitution in the original inverse edge coordinate. -/
def arithmeticFifthInitialLastEdgeIso (b a : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (A b a) ≪≫ (edgeInversion Q).symm

local notation "K" => arithmeticFifthInitialLastEdgeIso hπ data H m j hj u hu

/-- The closing overlap carries the full conjugated outgoing retained substitution. -/
@[reassoc] theorem arithmeticFifthInitialLastOrientedIso_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (C b).hom = (K b true).hom ≫ L ≫ (O b).hom := by
  have h := arithmeticFifthInitialLastIso_puncture hπ data H m j hj u hu b true
  have ho := arithmeticFifthInitialLastOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_true] at h
  simp only [arithmeticFifthInitialLastEdgeIso, Iso.trans_hom, Iso.symm_hom,
    arithmeticClosingRetainedBoundary, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (leftBranchOpen Q τ), h, Category.assoc]

/-- The incoming edge carries its own full opposite-puncture substitution. -/
@[reassoc] theorem arithmeticFifthInitialLastOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (C b).hom =
      (K b false).hom ≫ precedingBranch Q τ ≫ (O b).hom := by
  have h := arithmeticFifthInitialLastIso_puncture hπ data H m j hj u hu b false
  have ho := arithmeticFifthInitialLastOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_false] at h
  simp only [arithmeticFifthInitialLastEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (rightBranchOpen Q τ), h, Category.assoc]

/-- The whole joint edge formula gives exactly its oriented geometric edge. -/
theorem arithmeticFifthInitialLastEdgeEquiv_spec (b a : Bool) :
    punctureSpecIso (arithmeticFifthInitialLastEdgeEquiv hπ data H j hj u hu m b a) = K b a := by
  simp only [arithmeticFifthInitialLastEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticFifthInitialLastEdgeIso]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
