/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionAlgebra

/-!
# Successor action lifts on the constructed fraction/divided atlas

Apply the normalized depth lift to the actual affine presentations, whose
flatness and original-action equations have been proved. Insertion in the
whole first finite model preserves its exact step contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "C" => BlowupFractionChart.chart I f
local notation "c" => finiteSuccessiveFractionChart hπ data 0 hn f hf
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstFractionCover hπ data hn f hf


local notation "E" => initialExterior d

/-- An actual local successor lift on each constructed affine input/output presentation. -/
def firstFractionLocalAction (i : (U).I₀) : Spec ((U).X i) ⟶
    WeierstrassSuccessiveX.depthStep π (start + 0) W (e).b3 (e).b4 (e).b6 :=
  depthLocalAction (S := (U).X i) hπ d e (firstFractionParameter hπ data hn f hf i)
    (firstFractionAlphaAlg hπ data hn f hf i) (firstFractionBetaAlg hπ data hn f hf i)
    (firstFractionAlg_parameter hπ data hn f hf i)
    (firstFractionAlg_addition hπ data hn f hf i) f hf
    (firstFractionHom hπ data hn f hf i) (firstFractionBetaAlg_factor hπ data hn f hf i)
    (firstFractionHom_flat hπ data hn f hf i)

/-- The local lift retains precisely the actual divided output projection. -/
@[reassoc] theorem firstFractionLocalAction_contraction (i : (U).I₀) :
    firstFractionLocalAction hπ data hn f hf i ≫ localContraction hπ d e =
      firstFractionDividedOutput hπ data hn f hf i ≫ (previousChartIso hπ d e).hom := by
  rw [firstFractionLocalAction, depthLocalAction_contraction]
  exact congrArg (fun t => t ≫ (previousChartIso hπ d e).hom)
    (firstFractionAlpha_spec hπ data hn f hf i)

/-- Insert the actual affine lift into the complete first finite model. -/
def firstFractionAction (i : (U).I₀) :
    Spec ((U).X i) ⟶ finiteGlobalModel hπ data 1 hn :=
  firstFractionLocalAction hπ data hn f hf i ≫
    pushout.inr (E).attach (localBoundary hπ d e) ≫ ((E).advanceIso hπ e).inv ≫
      finiteLocalChart hπ data 1 hn

/-- The global step of each constructed lift is its actual divided output. -/
@[reassoc] theorem firstFractionAction_step (i : (U).I₀) :
    firstFractionAction hπ data hn f hf i ≫ finiteGlobalStep hπ data 0 hn =
      firstFractionDividedOutput hπ data hn f hf i ≫ v := by
  rw [firstFractionAction, Category.assoc, Category.assoc, Category.assoc,
    finiteGlobalStep_local]
  change _ ≫ _ ≫ ((E).advanceIso hπ e).inv ≫ (E).stepContraction hπ e ≫ _ = _
  rw [← Exterior.advanceIso_contraction, Category.assoc, Iso.inv_hom_id_assoc,
    Exterior.localReplacement_inr_contraction_assoc, firstFractionLocalAction_contraction_assoc]
  rfl

/-- Every local successor lift contracts to the already constructed stage-zero action. -/
@[reassoc] theorem firstFractionAction_output (i : (U).I₀) :
    firstFractionAction hπ data hn f hf i ≫ finiteGlobalStep hπ data 0 hn =
      (U).f i ≫ pullback.fst _ _ ≫ firstFractionOutput hπ data hn f hf := by
  rw [firstFractionAction_step, firstFractionDividedOutput, Category.assoc,
    ← pullback.condition]

/-- Contracting a local successor lift gives exactly the original prescribed whole-input action. -/
@[reassoc] theorem firstFractionAction_original (i : (U).I₀) :
    firstFractionAction hπ data hn f hf i ≫ finiteGlobalContraction hπ data 1 hn =
      (U).f i ≫ pullback.fst _ _ ≫ firstFractionInput hπ data hn f hf ≫
        finiteGlobalActionInput hπ data 1 hn ≫ leftSmoothFactorAddition W := by
  rw [← finiteGlobalStep_contraction hπ data 0 hn, firstFractionAction_output_assoc]
  simp only [firstFractionOutput, Category.assoc, firstActionOutput_contraction]

end FLT.Mazur.WeierstrassDividedDepth
