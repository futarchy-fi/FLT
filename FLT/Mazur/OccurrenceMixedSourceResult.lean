/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OccurrenceMixedSourceRefinement

/-!
# A bounded interface for the simultaneous refinement result

Name the complete refinement proposition so geometric applications can be
elaborated separately from extraction of their coordinates and restrictions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

open IteratedQuotientProjection

attribute [local irreducible] oldDenominatorEquiv oldDenominatorProjection
  oldDenominatorOriginalProjection oldDenominatorRepresentative

universe u v w e h q

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) {O : ι → Type q} [∀ i, Finite (O i)]
  (r : ∀ i, O i → MvPolynomial (Fin (n i)) R)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  (s b : ∀ i, Finset (I i))
  {J : ∀ i, O i → Type w} [∀ i o, Finite (J i o)]
  (d : ∀ i o, J i o → FiniteRelationLocalization.Stage (I i) (r i o) (s i))
  {E : ∀ (_ : ι) j, O j → Type e} [∀ i j o, Finite (E i j o)]
  {H : ∀ (_ : ι) j o, J j o → Type h} [∀ i j o k, Finite (H i j o k)]
  (src : ∀ i j o, E i j o → O i)
  (src₂ : ∀ i j o k, H i j o k → O i)
  (cF : ∀ i j o, E i j o → Finset (I i))
  (cG : ∀ i j o k, H i j o k → Finset (I i))

/-- Shared stages and both arrow levels, with old and original recovery squares. -/
def OccurrenceMixedSourceRefinementResult
    (hcF : ∀ i j o a, cF i j o a ≤ s i)
    (hcG : ∀ i j o k a, cG i j o k a ≤ s i)
    (F : ∀ i j o (a : E i j o),
      FiniteRelationLocalization.Quotient (I i) (r i (src i j o a)) →ₐ[R]
        FiniteRelationLocalization.Quotient (I j) (r j o))
    (G : ∀ i j o k (a : H i j o k),
      FiniteRelationLocalization.Quotient (I i) (r i (src₂ i j o k a)) →ₐ[R]
        FiniteRelationIterated.Quotient R (I j) (r j o) (s j) (d j o k))
    (Fₛ : ∀ i j o (a : E i j o),
      FiniteRelationLocalization.Stage (I i) (r i (src i j o a)) (cF i j o a) →ₐ[R]
        FiniteRelationLocalization.Stage (I j) (r j o) (s j))
    (Gₛ : ∀ i j o k (a : H i j o k),
      FiniteRelationLocalization.Stage (I i) (r i (src₂ i j o k a)) (cG i j o k a) →ₐ[R]
        FiniteRelationIterated.Stage R (I j) (r j o) (s j) (d j o k) ⟨s j, le_refl (s j)⟩)
    : Prop :=
    ∃ (t : ∀ i, Finset (I i)) (hst : s ≤ t), b ≤ t ∧
      ∃ (Fₜ : ∀ i j o (a : E i j o),
          FiniteRelationLocalization.Stage (I i) (r i (src i j o a)) (t i) →ₐ[R]
            FiniteRelationLocalization.Stage (I j) (r j o) (t j))
        (Gₜ : ∀ i j o k (a : H i j o k),
          FiniteRelationLocalization.Stage (I i) (r i (src₂ i j o k a)) (t i) →ₐ[R]
            FiniteRelationIterated.Stage R (I j) (r j o) (s j) (d j o k) ⟨t j, hst j⟩),
        (∀ i j o a, (Fₜ i j o a).comp
          (FiniteRelationLocalization.transition R (I i) (r i (src i j o a))
            ((hcF i j o a).trans (hst i))) =
            (FiniteRelationLocalization.transition R (I j) (r j o) (hst j)).comp (Fₛ i j o a)) ∧
        (∀ i j o k a, (Gₜ i j o k a).comp
          (FiniteRelationLocalization.transition R (I i) (r i (src₂ i j o k a))
            ((hcG i j o k a).trans (hst i))) =
            (FiniteRelationIterated.transition R (I j) (r j o) (s j) (d j o k)
              (show (⟨s j, le_refl (s j)⟩ : Set.Ici (s j)) ≤ ⟨t j, hst j⟩ from hst j)).comp
                (Gₛ i j o k a)) ∧
        (∀ i j o a, (FiniteRelationLocalization.toQuotient R (I j) (r j o) (t j)).comp
          (Fₜ i j o a) = (F i j o a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i (src i j o a)) (t i))) ∧
        ∀ i j o k a, (FiniteRelationIterated.toQuotient R (I j) (r j o) (s j) (d j o k)
          ⟨t j, hst j⟩).comp (Gₜ i j o k a) = (G i j o k a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i (src₂ i j o k a)) (t i))

/-- The simultaneous polynomial construction supplies the named result proposition. -/
theorem exists_occurrence_mixed_source_refinement_result
    (hcF : ∀ i j o a, cF i j o a ≤ s i)
    (hcG : ∀ i j o k a, cG i j o k a ≤ s i)
    (F : ∀ i j o (a : E i j o),
      FiniteRelationLocalization.Quotient (I i) (r i (src i j o a)) →ₐ[R]
        FiniteRelationLocalization.Quotient (I j) (r j o))
    (G : ∀ i j o k (a : H i j o k),
      FiniteRelationLocalization.Quotient (I i) (r i (src₂ i j o k a)) →ₐ[R]
        FiniteRelationIterated.Quotient R (I j) (r j o) (s j) (d j o k))
    (Fₛ : ∀ i j o (a : E i j o),
      FiniteRelationLocalization.Stage (I i) (r i (src i j o a)) (cF i j o a) →ₐ[R]
        FiniteRelationLocalization.Stage (I j) (r j o) (s j))
    (Gₛ : ∀ i j o k (a : H i j o k),
      FiniteRelationLocalization.Stage (I i) (r i (src₂ i j o k a)) (cG i j o k a) →ₐ[R]
        FiniteRelationIterated.Stage R (I j) (r j o) (s j) (d j o k) ⟨s j, le_refl (s j)⟩)
    (hFₛ : ∀ i j o a, (FiniteRelationLocalization.toQuotient R (I j) (r j o) (s j)).comp
      (Fₛ i j o a) = (F i j o a).comp
        (FiniteRelationLocalization.toQuotient R (I i) (r i (src i j o a)) (cF i j o a)))
    (hGₛ : ∀ i j o k a, (FiniteRelationIterated.toQuotient R (I j) (r j o) (s j) (d j o k)
      ⟨s j, le_refl (s j)⟩).comp (Gₛ i j o k a) = (G i j o k a).comp
        (FiniteRelationLocalization.toQuotient R (I i) (r i (src₂ i j o k a)) (cG i j o k a))) :
    OccurrenceMixedSourceRefinementResult n r I s b d src src₂ cF cG
      hcF hcG F G Fₛ Gₛ :=
  exists_occurrence_mixed_source_refinement n r I s b d src src₂ cF cG
    hcF hcG F G Fₛ Gₛ hFₛ hGₛ

end FLT.Mazur.FinitePolynomialCoefficients
