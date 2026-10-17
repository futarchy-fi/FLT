/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowJointGeometry
public import FLT.Mazur.WeierstrassDividedFifthShallowResidualAlgebra
public import FLT.Mazur.WeierstrassDividedFourthTransitions

/-!
# Geometric transitions for the full fifth depth-two corrections

The two last-node edges and the predecessor incoming edge use the complete
fifth factors. Their algebraic coordinate changes agree with the geometric ones.
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
  (arithmeticFifthShallowLastIntegralField hπ data H j hj u hu b)
local notation "S" => fun b ↦ twoBranchCorrectionRebasedPunctureFactor R π m
  (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m)
    (arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu) b
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticFifthShallowLastOrientedIso hπ data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m

/-- Express either retained puncture substitution in the original inverse edge coordinate. -/
def arithmeticFifthShallowLastEdgeIso (b a : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (A b a) ≪≫ (edgeInversion Q).symm

local notation "K" => arithmeticFifthShallowLastEdgeIso hπ data H m j hj u hu

/-- The closing overlap carries the full conjugated outgoing retained substitution. -/
@[reassoc] theorem arithmeticFifthShallowLastOrientedIso_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (C b).hom = (K b true).hom ≫ L ≫ (O b).hom := by
  have h := arithmeticFifthShallowLastIso_puncture hπ data H m j hj u hu b true
  have ho := arithmeticFifthShallowLastOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_true] at h
  simp only [arithmeticFifthShallowLastEdgeIso, Iso.trans_hom, Iso.symm_hom,
    arithmeticClosingRetainedBoundary, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (leftBranchOpen Q τ), h, Category.assoc]

/-- The incoming edge carries its own full opposite-puncture substitution. -/
@[reassoc] theorem arithmeticFifthShallowLastOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (C b).hom =
      (K b false).hom ≫ precedingBranch Q τ ≫ (O b).hom := by
  have h := arithmeticFifthShallowLastIso_puncture hπ data H m j hj u hu b false
  have ho := arithmeticFifthShallowLastOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_false] at h
  simp only [arithmeticFifthShallowLastEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (rightBranchOpen Q τ), h, Category.assoc]

/-- The whole joint edge formula gives exactly its oriented geometric edge. -/
theorem arithmeticFifthShallowLastEdgeEquiv_spec (b a : Bool) :
    punctureSpecIso (arithmeticFifthShallowLastEdgeEquiv hπ data H j hj u hu m b a) = K b a := by
  simp only [arithmeticFifthShallowLastEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticFifthShallowLastEdgeIso]
  rfl

local notation "s" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFifthShallowPrecedingSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFifthShallowPrecedingIntegralField hπ data H j hj u hu

/-- The predecessor's opposite correction in its original incoming edge coordinate. -/
def arithmeticFifthShallowPrecedingEdgeIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫
    punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (V b) false) ≪≫
      (edgeInversion Q).symm

local notation "Kₚ" => arithmeticFifthShallowPrecedingEdgeIso hπ data H m j hj u hu

/-- The opposite predecessor puncture retains both its fourth and fifth smoothing. -/
@[reassoc] theorem arithmeticFifthShallowPrecedingIso_incoming (b : Bool) :
    precedingBranch Q (s b) ≫ (arithmeticFifthShallowPrecedingIso hπ data H m j hj u hu b).hom =
      (Kₚ b).hom ≫ precedingBranch Q (t b) := by
  have h := arithmeticFifthShallowPrecedingIso_puncture hπ data H m j hj u hu b false
  simp only [punctureOpen_false] at h
  simp only [arithmeticFifthShallowPrecedingEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The algebraic opposite substitution gives the exact incoming geometric correction. -/
theorem arithmeticFifthShallowPrecedingEdgeEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFifthShallowPrecedingEdgeEquiv hπ data H j hj u hu m b) = Kₚ b := by
  simp only [arithmeticFifthShallowPrecedingEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticFifthShallowPrecedingEdgeIso]
  rfl


end FLT.Mazur.WeierstrassDividedDepth
