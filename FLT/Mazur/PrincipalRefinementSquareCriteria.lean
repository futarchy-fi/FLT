/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientDiagramRefinement

/-!
# Principal refinement squares from representative formulas

Equality on polynomial numerators proves squares on the entire localized ring.
These criteria keep simultaneous diagram constructions small to elaborate.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R]
  {P : Type v} [CommRing P] [Algebra R P] (I : Ideal P) (a : P)
  {Q : Type w} [CommRing Q] [Algebra R Q] (J : Ideal Q) (r : Q)
  {s t : Finset I} {b c : Finset J} (hst : s ≤ t) (hbc : b ≤ c)

/-- Numerator formulas for the same representatives imply the full old principal square. -/
theorem principal_old_square_of_representatives
    (f : P → Localization.Away r)
    (G : FiniteRelationLocalization.Stage I a s →ₐ[R]
      FiniteRelationLocalization.Stage J r b)
    (H : FiniteRelationLocalization.Stage I a t →ₐ[R]
      FiniteRelationLocalization.Stage J r c)
    (hG : ∀ p, PrincipalQuotientProjection.projection (FiniteRelationModel.relations J b) r
      (f p) = G (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I s) p)))
    (hH : ∀ p, H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)) =
      PrincipalQuotientProjection.projection (FiniteRelationModel.relations J c) r (f p)) :
    H.comp (FiniteRelationLocalization.transition R I a hst) =
      (FiniteRelationLocalization.transition R J r hbc).comp G := by
  apply AlgHom.coe_ringHom_injective
  apply PrincipalQuotientProjection.hom_ext (FiniteRelationModel.relations I s) a
  intro p
  change H (FiniteRelationLocalization.transition R I a hst
    (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I s) p))) =
    FiniteRelationLocalization.transition R J r hbc
      (G (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I s) p)))
  rw [FiniteRelationLocalization.transition_algebraMap, FiniteRelationModel.transition_mk,
    hH, ← hG, principal_transition_projection]

/-- Finite and original numerator formulas imply recovery of the entire principal arrow. -/
theorem principal_recovery_of_representatives
    (f : P → Localization.Away r)
    (F : FiniteRelationLocalization.Quotient I a →ₐ[R]
      FiniteRelationLocalization.Quotient J r)
    (H : FiniteRelationLocalization.Stage I a t →ₐ[R]
      FiniteRelationLocalization.Stage J r c)
    (hF : ∀ p, PrincipalQuotientProjection.projection J r (f p) =
      F (algebraMap _ _ (Ideal.Quotient.mk I p)))
    (hH : ∀ p, H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)) =
      PrincipalQuotientProjection.projection (FiniteRelationModel.relations J c) r (f p)) :
    (FiniteRelationLocalization.toQuotient R J r c).comp H =
      F.comp (FiniteRelationLocalization.toQuotient R I a t) := by
  apply AlgHom.coe_ringHom_injective
  apply PrincipalQuotientProjection.hom_ext (FiniteRelationModel.relations I t) a
  intro p
  change FiniteRelationLocalization.toQuotient R J r c
    (H (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p))) =
    F (FiniteRelationLocalization.toQuotient R I a t
      (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations I t) p)))
  rw [hH, FiniteRelationLocalization.toQuotient_projection,
    FiniteRelationLocalization.toQuotient_algebraMap]
  exact hF p

end FLT.Mazur.FinitePolynomialCoefficients
