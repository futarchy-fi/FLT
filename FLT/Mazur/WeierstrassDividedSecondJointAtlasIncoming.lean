/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointAtlasClosing
public import FLT.Mazur.WeierstrassDividedResidualLiftIncomingGeometry

/-!
# Actual incoming squares in the simultaneous second atlas

At positive retained depth the predecessor and shared last node use their
installed corrections. The full joint residual is their actual overlap map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticSecondPrecedingOrientedIso arithmeticSecondJointAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (a : ℕ) (ha : a + 1 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticSecondJointAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticSecondJointAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "P" => arithmeticSecondPrecedingOrientedIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "N" => arithmeticSecondJointLastIdentification hπ data H m j hj u hu
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu

/-- The predecessor label has exactly its changed smoothing. -/
def arithmeticSecondJointPrecedingIdentification (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ A (.retained ⟨a, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticSecondJointAtlasObject, ha, ↓reduceIte])

local notation "M" => arithmeticSecondJointPrecedingIdentification hπ data H m j hj u hu a ha

omit [IsBezout R] in
/-- The installed predecessor is precisely the full changed-smoothing correction. -/
theorem arithmeticSecondJointAtlasCorrection_preceding (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) = P b ≪≫ M b := by
  simp only [arithmeticSecondJointAtlasCorrection, ha, ↓reduceDIte]
  rfl

/-- The predecessor comparison recovers its full previous chart inclusion. -/
@[reassoc] theorem arithmeticSecondJointPreceding_chart (b : Bool) :
    (P b).hom ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      κ (.retained ⟨a, by omega⟩ b) := by
  rw [← Category.assoc, ← Iso.trans_hom, ← arithmeticSecondJointAtlasCorrection_preceding,
    arithmeticSecondJointAtlasCorrection_chart]

/-- The installed incoming edge has precisely the full joint algebra residual's geometry. -/
@[reassoc] theorem arithmeticSecondJointAtlas_residual_incoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticSecondJointIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N b).hom ≫
          ι (.retained ⟨j, by omega⟩ b) := by
  apply (cancel_epi
    (punctureSpecIso (arithmeticSecondPrecedingPuncture hπ data H m j hj u hu b)).hom).mp
  calc
    _ = leftBranchOpen Q τ ≫ (O b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)),
        ← arithmeticSecondPrecedingOrientedIso_outgoing, Category.assoc, Category.assoc,
        arithmeticSecondJointPreceding_chart]
    _ = (arithmeticResidualLiftEdgeIso hπ data H m j hj u hu b false).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ κ (.retained ⟨j, by omega⟩ b) :=
      arithmeticResidualLiftAtlas_residual_incoming hπ data H m j hj u hu a ha b
    _ = _ := by
      simp only [arithmeticSecondJointIncomingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticSecondJointOrientedIso_incoming_assoc,
        arithmeticSecondJointLast_chart]

omit m in
/-- Both installed incoming errors vanish at stage two with the same shared closing nodes. -/
@[reassoc] theorem arithmeticSecondJointAtlas_incoming_second (b : Bool) :
    leftBranchOpen (Quotient R π 2)
        (arithmeticSecondPrecedingSmoothing hπ data H 2 j hj u hu b) ≫
      (arithmeticSecondJointPrecedingIdentification hπ data H 2 j hj u hu a ha b).hom ≫
        arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 2)
          (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 2) ≫
        (twistedRetainedOrientation data H 2 b).hom ≫
          (arithmeticSecondJointLastIdentification hπ data H 2 j hj u hu b).hom ≫
            arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu
              (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticSecondJointAtlas_residual_incoming hπ data H 2 j hj u hu a ha b
  rw [← arithmeticSecondJointIncomingEquiv_spec, arithmeticSecondJointIncomingEquiv_second,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
