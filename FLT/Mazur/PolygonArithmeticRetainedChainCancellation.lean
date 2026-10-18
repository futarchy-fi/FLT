/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainPunctures
public import FLT.Mazur.PolygonArithmeticRetainedChainRestriction
public import FLT.Mazur.PolygonArithmeticSimultaneousCancellation

/-!
# Cancel every retained-chain residual using its constructed next field

The next fields are extracted from the actual compatible preceding residuals.
At every index they normalize every edge using shared retained factors and one common
terminal; the initial edge retains its entire original reciprocal base.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
open PolygonArithmeticSimultaneous
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (B : (m : ℕ) → (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])

variable (S : State R π n) (hS : S.Compatible) (hB : CompatibleEquiv B)
  (r : ℕ) (hr : S.Normalized B r)
local notation "q" => S.nextIntegralField B hS hB r hr
local notation "e" => S.nextField B hS hB r hr
local notation "V" => retainedInput (π := π) r q
local notation "T" => terminalInput (π := π) r q

/-- The complete next initial residual equals the same full original base. -/
theorem State.next_initial (ha : S.Annihilated) (hb : ReciprocalBase B) (b : Bool) :
    (S.step r q).edgeEquiv .initial (r + 1) b = B (r + 1) := by
  change ((twoBranchCorrectionPunctureFactor R π (r + 1) _ (V 0 b) false).trans
    (S.edgeEquiv .initial (r + 1) b)).trans
      (correctionPunctureFactor R π (r + 1) _ (initialInput (π := π) r q b) true).symm = _
  rw [S.initialPuncture_next, S.retainedPuncture_next r q ha, retainedField_incoming_spec]
  simp only [incomingEdge_zero, S.nextIntegralField_spec B hS hB r hr]
  apply LaurentReciprocalRelativeCorrection.cancel_relative (parameter R π (r + 1)) (r + 1)
    (nextCorrectionParameter_square R π r)
  · exact hb (r + 1)
  · change ((Ideal.span {parameter R π (r + 1)}).map (algebraMap _ _)) ^
      (1 + (r + 1)) = ⊥
    rw [Nat.add_comm 1, ← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow,
      Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    exact S.nextField_subst B hS hB r hr .initial b

/-- The complete closing error factors through the actual common terminal and last node. -/
theorem State.next_closing_factorization (ha : S.Annihilated) (b : Bool) :
    S.edgeEquiv .closing (r + 1) b =
      (twoBranchCorrectionRebasedPunctureFactor R π (r + 1)
        (S.terminal (r + 1)) T b).trans (S.outgoingFactor r q (r + 1) (Fin.last n) b) := by
  rw [S.terminalPuncture_next r q ha, S.outgoingFactor_next r q ha, outgoingEdge_last]
  simp only [S.nextIntegralField_spec B hS hB r hr]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := S.nextField_subst B hS hB r hr .closing b
  change (S.edgeEquiv .closing (r + 1) b).toAlgHom = _ at h
  rw [h]
  change _ = (LaurentSquareZeroAutomorphism.subst _ _
    (LaurentBoundaryCorrectionSplit.nonpositivePart _)).comp
      (LaurentSquareZeroAutomorphism.subst _ _ (LaurentBoundaryCorrectionSplit.positivePart _))
  rw [LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  exact (LaurentBoundaryCorrectionSplit.parts_add (e .closing b)).symm.trans (add_comm _ _)

/-- Both full closing residuals vanish using the same last factor and common terminal. -/
theorem State.next_closing (ha : S.Annihilated) (b : Bool) :
    (S.step r q).edgeEquiv .closing (r + 1) b = AlgEquiv.refl := by
  change ((twoBranchCorrectionRebasedPunctureFactor R π (r + 1) _ T b).symm.trans
    (S.edgeEquiv .closing (r + 1) b)).trans (S.outgoingFactor r q (r + 1) (Fin.last n) b).symm = _
  rw [S.next_closing_factorization B hS hB r hr ha]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.coe_refl, id_eq]

/-- The full internal error cancels using the same factors as its two neighboring edges. -/
theorem State.next_incoming (ha : S.Annihilated) (i : Fin n) (b : Bool) :
    (S.step r q).edgeEquiv (.incoming i) (r + 1) b = AlgEquiv.refl := by
  have hsplit :
      (twoBranchCorrectionPunctureFactor R π (r + 1)
        (S.retained (r + 1) i.succ b) (V i.succ b) false).trans
          (S.edgeEquiv (.incoming i) (r + 1) b) =
            S.outgoingFactor r q (r + 1) i.castSucc b := by
    rw [S.retainedPuncture_next r q ha, retainedField_incoming_spec,
      S.outgoingFactor_next r q ha, incomingEdge_succ, outgoingEdge_castSucc]
    simp only [S.nextIntegralField_spec B hS hB r hr]
    apply AlgEquiv.coe_toAlgHom_injective
    have h := S.nextField_subst B hS hB r hr (.incoming i) b
    change (S.edgeEquiv (.incoming i) (r + 1) b).toAlgHom = _ at h
    change (S.edgeEquiv (.incoming i) (r + 1) b).toAlgHom.comp
      (LaurentSquareZeroAutomorphism.subst _ _ (-_)) = _
    rw [h, LaurentSquareZeroAutomorphism.subst_comp]
    congr 1
    exact (sub_eq_add_neg _ _).symm
  change ((twoBranchCorrectionPunctureFactor R π (r + 1) _ _ false).trans
    (S.edgeEquiv (.incoming i) (r + 1) b)).trans
      (S.outgoingFactor r q (r + 1) i.castSucc b).symm = _
  rw [hsplit]
  ext z : 1
  exact (S.outgoingFactor r q (r + 1) i.castSucc b).symm_apply_apply z

/-- The constructed measured fields normalize every actual edge at the next layer. -/
theorem State.next_normalized (ha : S.Annihilated) (hb : ReciprocalBase B) :
    (S.step r q).Normalized B (r + 1) := by
  intro edge b
  cases edge with
  | initial => exact S.next_initial B hS hB r hr ha hb b
  | incoming i => exact S.next_incoming B hS hB r hr ha i b
  | closing => exact S.next_closing B hS hB r hr ha b

end FLT.Mazur.PolygonArithmeticRetainedChain
