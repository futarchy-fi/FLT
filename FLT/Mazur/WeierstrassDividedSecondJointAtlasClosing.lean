/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointAtlasEdges
public import FLT.Mazur.WeierstrassDividedSecondJointTransitions

/-!
# Actual closing squares in the simultaneous second atlas

The last retained label is identified with its unchanged smoothing. The
terminal label keeps the exact second rebased smoothing at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticSecondJointOrientedIso arithmeticSecondJointAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticSecondJointAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticSecondJointAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "C" => arithmeticSecondJointOrientedIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "F" => arithmeticSecondResidualLiftTerminalIso hπ data H m j hj u hu
local notation "s" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m
local notation "σ" => arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu

/-- The last label has its original smoothing, since it is not its own predecessor. -/
def arithmeticSecondJointLastIdentification (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ A (.retained ⟨j, by omega⟩ b) :=
  eqToIso (by
    dsimp only [arithmeticSecondJointAtlasObject]
    rw [ite_eq_right (show ¬j + 1 = j by omega)]
    rfl)

local notation "N" => arithmeticSecondJointLastIdentification hπ data H m j hj u hu

omit [IsBezout R] in
/-- The installed last-label correction is precisely the shared oriented correction. -/
theorem arithmeticSecondJointAtlasCorrection_last (b : Bool) :
    E (.retained ⟨j, by omega⟩ b) = C b ≪≫ N b := by
  simp only [arithmeticSecondJointAtlasCorrection,
    show ¬j + 1 = j by omega, ↓reduceDIte, ↓reduceIte]
  rfl

/-- The normalized last-chart inclusion is the actual full corrected chart inclusion. -/
@[reassoc] theorem arithmeticSecondJointLast_chart (b : Bool) :
    (C b).hom ≫ (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      κ (.retained ⟨j, by omega⟩ b) := by
  rw [← Category.assoc, ← Iso.trans_hom, ← arithmeticSecondJointAtlasCorrection_last,
    arithmeticSecondJointAtlasCorrection_chart]

/-- Both installed closing overlaps have the full joint residual, at every arithmetic order. -/
@[reassoc] theorem arithmeticSecondJointAtlas_residual_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (arithmeticSecondJointClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen s b ≫ ι .terminal := by
  have ht := arithmeticSecondJointAtlasCorrection_chart hπ data H m j hj u hu .terminal
  change (F).hom ≫ ι .terminal = κ .terminal at ht
  apply (cancel_epi (arithmeticSecondJointEdgeIso hπ data H m j hj u hu b true).hom).mp
  calc
    _ = (L ≫ (O b).hom) ≫ κ (.retained ⟨j, by omega⟩ b) := by
      rw [← Category.assoc _ (L ≫ (O b).hom),
        ← arithmeticSecondJointOrientedIso_closing, Category.assoc, Category.assoc,
        arithmeticSecondJointLast_chart, Category.assoc]
    _ = (arithmeticResidualLiftClosingResidual hπ data H m j hj u hu b).hom ≫
        punctureOpen σ b ≫ κ .terminal :=
      arithmeticResidualLiftAtlas_residual_closing hπ data H m j hj u hu b
    _ = _ := by
      simp only [arithmeticSecondJointClosingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticSecondResidualLiftTerminalIso_puncture_assoc, ht]

omit m in
/-- At stage two both closing overlaps are the standard complete punctures in this atlas. -/
@[reassoc] theorem arithmeticSecondJointAtlas_closing_second (b : Bool) :
    (arithmeticClosingRetainedBoundary data H 2 ≫
        (twistedRetainedOrientation data H 2 b).hom) ≫
      (arithmeticSecondJointLastIdentification hπ data H 2 j hj u hu b).hom ≫
        arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu (.retained ⟨j, by omega⟩ b) =
      punctureOpen (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu 2) b ≫
        arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu .terminal := by
  have h := arithmeticSecondJointAtlas_residual_closing hπ data H 2 j hj u hu b
  rw [← arithmeticSecondJointClosingEquiv_spec, arithmeticSecondJointClosingEquiv_second,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
