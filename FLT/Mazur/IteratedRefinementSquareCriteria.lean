/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedOldDenominatorRecovery

/-!
# Literal double-open refinement squares from representative formulas

The old denominator is fixed once. Equality on ambient numerators gives old
transition and original recovery squares on the entire source principal ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.IteratedQuotientProjection

universe u v w

variable {R : Type u} [CommRing R]
  {P : Type v} [CommRing P] [Algebra R P] (I : Ideal P) (a : P)
  {Q : Type w} [CommRing Q] [Algebra R Q] (J : Ideal Q) (r : Q)
  (b : Finset J) (d : FiniteRelationLocalization.Stage J r b)
  {s t : Finset I} {c e : Set.Ici b} (hst : s ≤ t) (hce : c ≤ e)

/-- Numerator formulas for literal old-coordinate targets imply the full old arrow square. -/
theorem old_square_of_representatives
    (f : P → Localization.Away (oldDenominatorRepresentative J r b d))
    (G : FiniteRelationLocalization.Stage I a s →ₐ[R]
      FiniteRelationIterated.Stage R J r b d c)
    (H : FiniteRelationLocalization.Stage I a t →ₐ[R]
      FiniteRelationIterated.Stage R J r b d e)
    (hG : ∀ p, oldDenominatorProjection R J r b d c (f p) =
      G (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I s) p)))
    (hH : ∀ p, H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)) =
      oldDenominatorProjection R J r b d e (f p)) :
    H.comp (FiniteRelationLocalization.transition R I a hst) =
      (FiniteRelationIterated.transition R J r b d hce).comp G := by
  apply AlgHom.coe_ringHom_injective
  apply PrincipalQuotientProjection.hom_ext (FiniteRelationModel.relations I s) a
  intro p
  change H (FiniteRelationLocalization.transition R I a hst
    (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I s) p))) =
    FiniteRelationIterated.transition R J r b d hce
      (G (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I s) p)))
  rw [FiniteRelationLocalization.transition_algebraMap, FiniteRelationModel.transition_mk,
    hH, ← hG]
  exact (AlgHom.congr_fun (oldDenominatorProjection_transition R J r b d hce) _).symm

/-- Finite and original literal numerator formulas imply recovery of the full iterated arrow. -/
theorem recovery_of_representatives
    (f : P → Localization.Away (oldDenominatorRepresentative J r b d))
    (F : FiniteRelationLocalization.Quotient I a →ₐ[R]
      FiniteRelationIterated.Quotient R J r b d)
    (H : FiniteRelationLocalization.Stage I a t →ₐ[R]
      FiniteRelationIterated.Stage R J r b d e)
    (hF : ∀ p, oldDenominatorOriginalProjection R J r b d (f p) =
      F (algebraMap _ _ (Ideal.Quotient.mk I p)))
    (hH : ∀ p, H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)) =
      oldDenominatorProjection R J r b d e (f p)) :
    (FiniteRelationIterated.toQuotient R J r b d e).comp H =
      F.comp (FiniteRelationLocalization.toQuotient R I a t) := by
  apply AlgHom.coe_ringHom_injective
  apply PrincipalQuotientProjection.hom_ext (FiniteRelationModel.relations I t) a
  intro p
  change FiniteRelationIterated.toQuotient R J r b d e
    (H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p))) =
    F (FiniteRelationLocalization.toQuotient R I a t
      (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)))
  rw [hH, FiniteRelationLocalization.toQuotient_algebraMap]
  rw [← AlgHom.comp_apply, oldDenominatorProjection_toQuotient]
  exact hF p

/-- Transport of a canonical target preserves every representative numerator formula. -/
theorem equiv_numerator_of_representatives
    (f : P → Localization.Away (oldDenominatorRepresentative J r b d))
    (H : FiniteRelationLocalization.Stage I a t →ₐ[R]
      Target (FiniteRelationModel.relations J e.val) r (oldDenominatorRepresentative J r b d))
    (hH : ∀ p, H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)) =
      projection (FiniteRelationModel.relations J e.val) r
        (oldDenominatorRepresentative J r b d) (f p)) (p : P) :
    ((oldDenominatorEquiv R J r b d e).toAlgHom.comp H)
      (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)) =
      oldDenominatorProjection R J r b d e (f p) := by
  change oldDenominatorEquiv R J r b d e
    (H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p))) = _
  rw [hH]
  exact AlgHom.congr_fun (oldDenominatorEquiv_comp_projection R J r b d e) _

end FLT.Mazur.IteratedQuotientProjection
