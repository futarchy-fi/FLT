/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OccurrenceOldDiagramRepresentatives
public import FLT.Mazur.PrincipalOldArrowRepresentatives
public import FLT.Mazur.OccurrenceOldTargetStages
public import FLT.Mazur.PrincipalRefinementSquareCriteria
public import FLT.Mazur.IteratedRefinementSquareCriteria

/-!
# Simultaneous refinement retaining old principal and double-open arrows

One ambient relation set per vertex refines both levels of an actual old
diagram. Second denominators remain the literal transitions of old coordinate
images. Every old arrow square and every original recovery square is retained.
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

/-- Cofinal shared refinements preserve both old arrow levels with literal coordinate targets. -/
theorem exists_occurrence_old_diagram_refinement
    (F : ∀ i j o (a : E i j o),
      FiniteRelationLocalization.Quotient (I i) (r i (src i j o a)) →ₐ[R]
        FiniteRelationLocalization.Quotient (I j) (r j o))
    (G : ∀ i j o k (a : H i j o k),
      FiniteRelationLocalization.Quotient (I i) (r i (src₂ i j o k a)) →ₐ[R]
        FiniteRelationIterated.Quotient R (I j) (r j o) (s j) (d j o k))
    (Fₛ : ∀ i j o (a : E i j o),
      FiniteRelationLocalization.Stage (I i) (r i (src i j o a)) (s i) →ₐ[R]
        FiniteRelationLocalization.Stage (I j) (r j o) (s j))
    (Gₛ : ∀ i j o k (a : H i j o k),
      FiniteRelationLocalization.Stage (I i) (r i (src₂ i j o k a)) (s i) →ₐ[R]
        FiniteRelationIterated.Stage R (I j) (r j o) (s j) (d j o k) ⟨s j, le_refl (s j)⟩)
    (hFₛ : ∀ i j o a, (FiniteRelationLocalization.toQuotient R (I j) (r j o) (s j)).comp
      (Fₛ i j o a) = (F i j o a).comp
        (FiniteRelationLocalization.toQuotient R (I i) (r i (src i j o a)) (s i)))
    (hGₛ : ∀ i j o k a, (FiniteRelationIterated.toQuotient R (I j) (r j o) (s j) (d j o k)
      ⟨s j, le_refl (s j)⟩).comp (Gₛ i j o k a) = (G i j o k a).comp
        (FiniteRelationLocalization.toQuotient R (I i) (r i (src₂ i j o k a)) (s i))) :
    ∃ (t : ∀ i, Finset (I i)) (hst : s ≤ t), b ≤ t ∧
      ∃ (Fₜ : ∀ i j o (a : E i j o),
          FiniteRelationLocalization.Stage (I i) (r i (src i j o a)) (t i) →ₐ[R]
            FiniteRelationLocalization.Stage (I j) (r j o) (t j))
        (Gₜ : ∀ i j o k (a : H i j o k),
          FiniteRelationLocalization.Stage (I i) (r i (src₂ i j o k a)) (t i) →ₐ[R]
            FiniteRelationIterated.Stage R (I j) (r j o) (s j) (d j o k) ⟨t j, hst j⟩),
        (∀ i j o a, (Fₜ i j o a).comp
          (FiniteRelationLocalization.transition R (I i) (r i (src i j o a)) (hst i)) =
            (FiniteRelationLocalization.transition R (I j) (r j o) (hst j)).comp (Fₛ i j o a)) ∧
        (∀ i j o k a, (Gₜ i j o k a).comp
          (FiniteRelationLocalization.transition R (I i) (r i (src₂ i j o k a)) (hst i)) =
            (FiniteRelationIterated.transition R (I j) (r j o) (s j) (d j o k)
              (show (⟨s j, le_refl (s j)⟩ : Set.Ici (s j)) ≤ ⟨t j, hst j⟩ from hst j)).comp
                (Gₛ i j o k a)) ∧
        (∀ i j o a, (FiniteRelationLocalization.toQuotient R (I j) (r j o) (t j)).comp
          (Fₜ i j o a) = (F i j o a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i (src i j o a)) (t i))) ∧
        ∀ i j o k a, (FiniteRelationIterated.toQuotient R (I j) (r j o) (s j) (d j o k)
          ⟨t j, hst j⟩).comp (Gₜ i j o k a) = (G i j o k a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i (src₂ i j o k a)) (t i)) := by
  classical
  obtain ⟨f, g, hfOld, hfFull, hf, hgOld, hgFull, hg, v, w, hv, hw⟩ :=
    exists_occurrence_old_diagram_representatives n r I s d src src₂ F G Fₛ Gₛ hFₛ hGₛ
  obtain ⟨t, hst, hbt, Fₜ, Gₜ, hFₜ, hGₜ⟩ :=
    exists_occurrence_old_target_stages n r I s b d src src₂ f g hf hg v hv w hw
  refine ⟨t, hst, hbt, Fₜ, Gₜ, ?_, ?_, ?_, ?_⟩
  · intro i j o a
    exact principal_old_square_of_representatives
      (s := s i) (t := t i) (b := s j) (c := t j)
      (I i) (r i (src i j o a)) (I j) (r j o) (hst i) (hst j)
      (f i j o a) (Fₛ i j o a) (Fₜ i j o a) (hfOld i j o a) (hFₜ i j o a)
  · intro i j o k a
    exact old_square_of_representatives
      (s := s i) (t := t i) (c := ⟨s j, le_refl (s j)⟩) (e := ⟨t j, hst j⟩)
      (I i) (r i (src₂ i j o k a)) (I j) (r j o) (s j) (d j o k) (hst i)
      (show (⟨s j, le_refl (s j)⟩ : Set.Ici (s j)) ≤ ⟨t j, hst j⟩ from hst j)
      (g i j o k a) (Gₛ i j o k a) (Gₜ i j o k a) (hgOld i j o k a) (hGₜ i j o k a)
  · intro i j o a
    exact principal_recovery_of_representatives (t := t i) (c := t j)
      (I i) (r i (src i j o a)) (I j) (r j o)
      (f i j o a) (F i j o a) (Fₜ i j o a) (hfFull i j o a) (hFₜ i j o a)
  · intro i j o k a
    exact recovery_of_representatives (t := t i) (e := ⟨t j, hst j⟩)
      (I i) (r i (src₂ i j o k a)) (I j) (r j o) (s j) (d j o k)
      (g i j o k a) (G i j o k a) (Gₜ i j o k a) (hgFull i j o k a) (hGₜ i j o k a)

end FLT.Mazur.FinitePolynomialCoefficients
