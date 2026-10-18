/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedClosingMap

/-!
# Exact original chart restrictions of the revised closing comparisons

The constructed original pair map retains all full retained corrections.
Both arms have literally the same corrected original terminal morphism,
so the terminal chart is available for the subsequent global assembly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H 1
local notation "D" => arithmeticTerminalChangedBoundary data H 1 j hj u hu
local notation "P" => fun (b : Bool) ↦
  ite (b = true) (leftBranchOpen Q σ) (rightBranchOpen Q σ)
local notation "I" => arithmeticFirstStandardClosingAttachmentIso hπ data H j hj u hu
local notation "A" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "F" => arithmeticFirstResidualTerminalIso hπ data H j hj u hu

/-- The standardization retains the full complementary correction on its original retained node. -/
@[reassoc] theorem arithmeticFirstStandardClosingAttachmentIso_retained (b : Bool) :
    pushout.inl L (D b) ≫ (I b).hom = (A b).hom ≫ pushout.inl L (P b) := by
  simp only [arithmeticFirstStandardClosingAttachmentIso, asIso_hom, pushout.map, pushout.inl_desc]

/-- Both standardized pairs restrict to the same whole terminal correction. -/
@[reassoc] theorem arithmeticFirstStandardClosingAttachmentIso_terminal (b : Bool) :
    pushout.inr L (D b) ≫ (I b).hom = (F).hom ≫ pushout.inr L (P b) := by
  simp only [arithmeticFirstStandardClosingAttachmentIso, asIso_hom, pushout.map, pushout.inr_desc]

local notation "l" => leftBranchOpen Q (parameter R π 1)
local notation "r" => arithmeticOriginalClosingBoundary data H 1 j hj
local notation "C" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "O" => twistedRetainedOrientation data H 1
local notation "c" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu
local notation "G" => arithmeticFirstOriginalRevisedClosingMap data H j hj u hu hπ

/-- The actual original retained chart uses its normalization, residual and orientation in order. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedClosingMap_retained (b : Bool) :
    pushout.inl l (r b) ≫ G b =
      (C).hom ≫ (A b).hom ≫ (O b).hom ≫ c ⟨j, by omega⟩ b := by
  rw [arithmeticFirstOriginalRevisedClosingMap, arithmeticFirstOriginalStandardClosingIso,
    Iso.trans_hom, Category.assoc, arithmeticChangedClosingAttachmentIso_retained_assoc,
    arithmeticFirstStandardClosingAttachmentIso_retained_assoc,
    arithmeticRevisedStandardClosingMap_retained]

local notation "dd" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "T" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 dd) (Data.b4 dd) (Data.b6 dd) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu 1
local notation "N" => arithmeticTerminalChangedIso data H 1 j hj u hu

/-- Both original terminal restrictions are the same complete three-stage correction. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedClosingMap_terminal (b : Bool) :
    pushout.inr l (r b) ≫ G b = (T ≪≫ N).hom ≫ (F).hom ≫ d := by
  rw [arithmeticFirstOriginalRevisedClosingMap, arithmeticFirstOriginalStandardClosingIso,
    Iso.trans_hom, Category.assoc, arithmeticChangedClosingAttachmentIso_terminal_assoc,
    arithmeticFirstStandardClosingAttachmentIso_terminal_assoc,
    arithmeticRevisedStandardClosingMap_terminal]

/-- The two independently mapped original attachments agree on their shared entire terminal. -/
theorem arithmeticFirstOriginalRevisedClosingMap_common_terminal :
    pushout.inr l (r false) ≫ G false = pushout.inr l (r true) ≫ G true := by
  rw [arithmeticFirstOriginalRevisedClosingMap_terminal,
    arithmeticFirstOriginalRevisedClosingMap_terminal]

end FLT.Mazur.WeierstrassDividedDepth
