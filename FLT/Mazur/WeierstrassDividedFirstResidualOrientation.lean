/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalFirstResidualGluing
public import FLT.Mazur.WeierstrassDividedTerminalChangedAtlas

/-!
# Residual corrections in the labeled retained orientation

Conjugating by the original branch orientation places the correction on the
actual labeled node. Its incoming puncture is fixed, including the reciprocal
parameter. This is the square needed at the last unchanged adjacent edge.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "O" => twistedRetainedOrientation data H 1
local notation "A" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "K" => arithmeticFirstResidualOverlapIso hπ data H j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H 1

/-- The whole retained correction in its original labeled branch orientation. -/
def arithmeticFirstResidualOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ A b ≪≫ O b

local notation "C" => arithmeticFirstResidualOrientedIso hπ data H j hj u hu

/-- Conjugation restores the full correction on the oriented closing chart. -/
@[reassoc] theorem arithmeticFirstResidualOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (C b).hom = (A b).hom ≫ (O b).hom := by
  simp only [arithmeticFirstResidualOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- The inverse correction uses the same original retained orientation. -/
@[reassoc] theorem arithmeticFirstResidualOrientedIso_inv (b : Bool) :
    (O b).hom ≫ (C b).inv = (A b).inv ≫ (O b).hom := by
  simp only [arithmeticFirstResidualOrientedIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- The exact closing square on the labeled retained chart, with its original overlap. -/
@[reassoc] theorem arithmeticFirstResidualOrientedIso_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (C b).hom = (K b).hom ≫ L ≫ (O b).hom := by
  rw [Category.assoc, arithmeticFirstResidualOrientedIso_hom,
    ← Category.assoc, arithmeticFirstResidualRetained_square, Category.assoc]

/-- The full incoming puncture is unchanged by the labeled correction. -/
@[reassoc] theorem arithmeticFirstResidualOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (C b).hom =
      precedingBranch Q τ ≫ (O b).hom := by
  rw [Category.assoc, arithmeticFirstResidualOrientedIso_hom,
    precedingBranch, Category.assoc, ← Category.assoc (rightBranchOpen Q τ),
    arithmeticFirstResidualRetainedIso_opposite, Category.assoc]

/-- The full incoming puncture is also unchanged by the inverse labeled correction. -/
@[reassoc] theorem arithmeticFirstResidualOrientedIso_incoming_inv (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (C b).inv =
      precedingBranch Q τ ≫ (O b).hom := by
  apply (cancel_mono (C b).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    arithmeticFirstResidualOrientedIso_incoming]

/-- The labeled closing reparametrization is invertible on the full overlap. -/
@[reassoc] theorem arithmeticFirstResidualOrientedIso_closing_inv (b : Bool) :
    (L ≫ (O b).hom) ≫ (C b).inv = (K b).inv ≫ L ≫ (O b).hom := by
  apply (cancel_mono (C b).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, arithmeticFirstResidualOrientedIso_closing,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
