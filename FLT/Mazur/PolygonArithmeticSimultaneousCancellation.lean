/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousPunctures
public import FLT.Mazur.PolygonArithmeticSimultaneousRestriction

/-!
# Simultaneous cancellation from the constructed next fields

The next fields are extracted from the actual compatible preceding residuals.
At every index they normalize both edges using one last factor and one common
terminal; the initial edge retains its entire original reciprocal base.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])

/-- The exact full base reduces to reciprocal transport modulo the parameter. -/
def ReciprocalBase : Prop :=
  ∀ m z, (B m).symm z - invert z ∈
    (Ideal.span {parameter R π m}).map (algebraMap (Quotient R π m) _)

variable (S : State R π) (hS : S.Compatible) (hB : CompatibleEquiv B)
  (r : ℕ) (hr : S.Normalized B r)
local notation "q" => S.nextIntegralField B hS hB r hr
local notation "e" => S.nextField B hS hB r hr
local notation "V" => lastInput (π := π) r q
local notation "T" => terminalInput (π := π) r q

/-- The complete next initial residual equals the same full original base. -/
theorem State.next_initial (ha : S.Annihilated) (hb : ReciprocalBase B) (b : Bool) :
    (S.step r q).initialEquiv (r + 1) b = B (r + 1) := by
  change ((twoBranchCorrectionPunctureFactor R π (r + 1) _ (V b) false).trans
    (S.initialEquiv (r + 1) b)).trans
      (correctionPunctureFactor R π (r + 1) _ (initialInput (π := π) r q b) true).symm = _
  rw [S.initialPuncture_next, S.lastPuncture_next r q ha, lastField_incoming_spec]
  simp only [S.nextIntegralField_spec B hS hB r hr]
  apply LaurentReciprocalRelativeCorrection.cancel_relative (parameter R π (r + 1)) (r + 1)
    (nextCorrectionParameter_square R π r)
  · exact hb (r + 1)
  · change ((Ideal.span {parameter R π (r + 1)}).map (algebraMap _ _)) ^
      (1 + (r + 1)) = ⊥
    rw [Nat.add_comm 1, ← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow,
      Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    exact S.nextField_subst B hS hB r hr false b

/-- The complete preceding closing error factors through the actual two next punctures. -/
theorem State.next_closing_factorization (ha : S.Annihilated) (b : Bool) :
    S.closingEquiv (r + 1) b =
      (twoBranchCorrectionRebasedPunctureFactor R π (r + 1)
        (S.terminal (r + 1)) T b).trans (S.lastEdge r q (r + 1) b) := by
  rw [State.lastEdge, S.terminalPuncture_next r q ha, S.lastPuncture_next r q ha,
    lastField_outgoing_spec]
  simp only [S.nextIntegralField_spec B hS hB r hr]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := S.nextField_subst B hS hB r hr true b
  change (S.closingEquiv (r + 1) b).toAlgHom = _ at h
  rw [h]
  change _ = (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
    (LaurentBoundaryVectorField.reciprocalField
      (LaurentBoundaryCorrectionSplit.nonpositivePart _))).comp invert.toAlgHom)).comp
      (LaurentSquareZeroAutomorphism.subst _ _ (LaurentBoundaryCorrectionSplit.positivePart _))
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal,
    LaurentBoundaryCorrectionSplit.reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  exact (LaurentBoundaryCorrectionSplit.parts_add (e true b)).symm.trans (add_comm _ _)

/-- Both full closing residuals vanish using the same last factor and common terminal. -/
theorem State.next_closing (ha : S.Annihilated) (b : Bool) :
    (S.step r q).closingEquiv (r + 1) b = AlgEquiv.refl := by
  change ((twoBranchCorrectionRebasedPunctureFactor R π (r + 1) _ T b).symm.trans
    (S.closingEquiv (r + 1) b)).trans (S.lastEdge r q (r + 1) b).symm = _
  rw [S.next_closing_factorization B hS hB r hr ha]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.coe_refl, id_eq]

/-- Constructing the measured fields advances simultaneous normalization by one layer. -/
theorem State.next_normalized (ha : S.Annihilated) (hb : ReciprocalBase B) :
    (S.step r q).Normalized B (r + 1) :=
  ⟨S.next_initial B hS hB r hr ha hb, S.next_closing B hS hB r hr ha⟩

end FLT.Mazur.PolygonArithmeticSimultaneous
