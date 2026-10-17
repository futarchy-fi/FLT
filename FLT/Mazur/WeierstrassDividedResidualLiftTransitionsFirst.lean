/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftTransitions
public import FLT.Mazur.WeierstrassDividedResidualLiftFirst

/-!
# First-layer reduction of the recomputed full transitions

The full closing reparametrization recovers the original first-order factor.
The incoming transition and corrected closing residual are the identity on
that layer. Higher-order vanishing is a separate filtration statement.
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
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H 1 j hj u hu
local notation "O" => twistedRetainedOrientation data H 1
local notation "L" => arithmeticClosingRetainedBoundary data H 1
local notation "K" => arithmeticResidualLiftEdgeIso hπ data H 1 j hj u hu
local notation "KI" => arithmeticFirstResidualOverlapIso hπ data H j hj u hu
local notation "E" => arithmeticResidualLiftClosingResidual hπ data H 1 j hj u hu

/-- The full lifted closing reparametrization recovers the original first-order overlap factor. -/
theorem arithmeticResidualLiftEdgeIso_closing_first (b : Bool) : K b true = KI b := by
  apply Iso.ext
  apply (cancel_mono (L ≫ (O b).hom)).mp
  have h := arithmeticResidualLiftOrientedIso_closing hπ data H 1 j hj u hu b
  rw [arithmeticResidualLiftOrientedIso_first,
    arithmeticFirstResidualOrientedIso_closing] at h
  simpa only [Category.assoc] using h.symm

/-- The full incoming transition reduces to the identity at first order. -/
theorem arithmeticResidualLiftEdgeIso_incoming_first (b : Bool) : K b false = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_mono (precedingBranch Q τ ≫ (O b).hom)).mp
  have h := arithmeticResidualLiftOrientedIso_incoming hπ data H 1 j hj u hu b
  rw [arithmeticResidualLiftOrientedIso_first,
    arithmeticFirstResidualOrientedIso_incoming] at h
  simpa only [Category.assoc, Iso.refl_hom, Category.id_comp] using h.symm

/-- The complete corrected closing residual is the identity on the first arithmetic layer. -/
theorem arithmeticResidualLiftClosingResidual_first (b : Bool) : E b = Iso.refl _ := by
  have hi := arithmeticResidualLiftTerminalSmoothing_first hπ data H j hj u hu
  have h := congrArg (fun f ↦ f ≫ (nodeParameterIso s σ hi).hom)
    (arithmeticResidualLiftTerminalIso_closing hπ data H 1 j hj u hu b)
  simp only [Category.assoc, punctureOpen_parameter] at h
  have hf := congrArg Iso.hom (arithmeticResidualLiftTerminalIso_first hπ data H j hj u hu)
  simp only [Iso.trans_hom] at hf
  rw [hf, arithmeticResidualLiftEdgeIso_closing_first] at h
  have ho := arithmeticFirstResidualTerminal_square hπ data H j hj u hu b
  have hp : (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) =
      punctureOpen σ b := by
    cases b
    · exact (punctureOpen_false _).symm
    · exact (punctureOpen_true _).symm
  rw [hp] at ho
  rw [ho] at h
  let _ : Mono (punctureOpen σ b) := by
    cases b
    · rw [punctureOpen_false]
      infer_instance
    · rw [punctureOpen_true]
      infer_instance
  apply Iso.ext
  apply (cancel_mono (punctureOpen σ b)).mp
  apply (cancel_epi (KI b).hom).mp
  simpa only [Category.assoc, Iso.refl_hom, Category.id_comp] using h.symm

end FLT.Mazur.WeierstrassDividedDepth
