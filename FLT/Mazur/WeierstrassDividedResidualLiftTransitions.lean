/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftPunctures
public import FLT.Mazur.WeierstrassDividedResidualLiftAtlasEdges

/-!
# Exact corrected closing residual and affected incoming transitions

The new closing transition is K inverse, then the original residual D, then
the full inverse terminal substitution S. The incoming retained transition
is separately constructed from its opposite puncture, with every term kept.
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
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu
local notation "A" => arithmeticResidualLiftRetainedPuncture hπ data H m j hj u hu
local notation "S" => arithmeticResidualLiftTerminalPuncture hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticResidualLiftOrientedIso hπ data H m j hj u hu
local notation "F" => arithmeticResidualLiftTerminalIso hπ data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "D" => arithmeticTerminalChangedBoundary data H m j hj u hu

/-- Express either retained puncture substitution in the original inverse edge coordinate. -/
def arithmeticResidualLiftEdgeIso (b a : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (A b a) ≪≫ (edgeInversion Q).symm

local notation "K" => arithmeticResidualLiftEdgeIso hπ data H m j hj u hu

/-- The closing overlap carries the full conjugated outgoing retained substitution. -/
@[reassoc] theorem arithmeticResidualLiftOrientedIso_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (C b).hom = (K b true).hom ≫ L ≫ (O b).hom := by
  have h := arithmeticResidualLiftOrientedIso_puncture hπ data H m j hj u hu b true
  rw [punctureOpen_true] at h
  simp only [arithmeticResidualLiftEdgeIso, Iso.trans_hom, Iso.symm_hom,
    arithmeticClosingRetainedBoundary, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (leftBranchOpen Q τ), h]

/-- The incoming edge carries its own full opposite-puncture substitution. -/
@[reassoc] theorem arithmeticResidualLiftOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (C b).hom =
      (K b false).hom ≫ precedingBranch Q τ ≫ (O b).hom := by
  have h := arithmeticResidualLiftOrientedIso_puncture hπ data H m j hj u hu b false
  rw [punctureOpen_false] at h
  simp only [arithmeticResidualLiftEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (rightBranchOpen Q τ), h]

/-- The actual residual after both lifted corrections, in geometric composition order. -/
def arithmeticResidualLiftClosingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (K b true).symm ≪≫ arithmeticTerminalResidualTwist data H m j hj u hu b ≪≫
    punctureSpecIso (S b).symm

local notation "E" => arithmeticResidualLiftClosingResidual hπ data H m j hj u hu

/-- The corrected terminal boundary has exactly the recomputed full closing residual. -/
@[reassoc] theorem arithmeticResidualLiftTerminalIso_closing (b : Bool) :
    D b ≫ (F).hom = (K b true).hom ≫ (E b).hom ≫ punctureOpen s b := by
  have hp : (if b then leftBranchOpen Q
        (arithmeticTerminalChangedSmoothing data H m j hj u hu)
      else rightBranchOpen Q (arithmeticTerminalChangedSmoothing data H m j hj u hu)) =
      punctureOpen (arithmeticTerminalChangedSmoothing data H m j hj u hu) b := by
    cases b
    · exact (punctureOpen_false _).symm
    · exact (punctureOpen_true _).symm
  simp only [arithmeticResidualLiftClosingResidual, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [arithmeticTerminalChangedBoundary, hp, Category.assoc,
    arithmeticResidualLiftTerminalIso_puncture]

variable [IsBezout R]
local notation "ι" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu

/-- Cancel the actual retained reparametrization in the full corrected atlas closing square. -/
@[reassoc] theorem arithmeticResidualLiftAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ ι (.retained ⟨j, by omega⟩ b) =
      (E b).hom ≫ punctureOpen s b ≫ ι .terminal := by
  apply (cancel_epi (K b true).hom).mp
  have h := arithmeticResidualLiftAtlas_closing hπ data H m j hj u hu b
  rw [← Category.assoc L (O b).hom (C b).hom,
    arithmeticResidualLiftOrientedIso_closing, arithmeticResidualLiftTerminalIso_closing] at h
  simpa only [Category.assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
