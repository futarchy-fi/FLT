/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedNormalizedAdjacent
public import FLT.Mazur.WeierstrassDividedResidualLiftTransitions

/-!
# The original incoming edge after the first full residual correction

A positive-depth predecessor remains unchanged. The incoming overlap on the
last retained node carries exactly the full opposite-puncture substitution.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "O" => twistedRetainedOrientation data H m
local notation "κ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "ι" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "C" => arithmeticResidualLiftOrientedIso hπ data H m j hj u hu

/-- The full incoming residual is the actual overlap with the retained predecessor. -/
@[reassoc] theorem arithmeticResidualLiftAtlas_residual_incoming
    (a : ℕ) (ha : a + 1 = j) (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticResidualLiftEdgeIso hπ data H m j hj u hu b false).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ ι (.retained ⟨j, by omega⟩ b) := by
  have hp := arithmeticResidualLiftAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨a, by omega⟩ b)
  have hl := arithmeticResidualLiftAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨j, by omega⟩ b)
  simp only [arithmeticResidualLiftAtlasCorrection, show ¬a = j by omega,
    ↓reduceIte, Iso.refl_hom, Category.id_comp] at hp
  simp only [arithmeticResidualLiftAtlasCorrection, ↓reduceIte] at hl
  change (C b).hom ≫ ι (.retained ⟨j, by omega⟩ b) = κ (.retained ⟨j, by omega⟩ b) at hl
  have h := changedArithmeticAtlas_normalized_adjacent hπ data H m j hj u hu a (by omega) b
  dsimp only [arithmeticResidualLiftAtlasObject, changedArithmeticAtlasObject,
    twistedArithmeticAtlasObject] at *
  rw [show (⟨a + 1, by omega⟩ : Fin (j + 1)) = ⟨j, by omega⟩ from Fin.ext ha] at h
  rw [← hp, ← hl] at h
  exact h.trans (arithmeticResidualLiftOrientedIso_incoming_assoc hπ data H m j hj u hu b
    (ι (.retained ⟨j, by omega⟩ b)))

end FLT.Mazur.WeierstrassDividedDepth
