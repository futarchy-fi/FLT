/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedOldDiagramRepresentatives
public import FLT.Mazur.PrincipalOldArrowRepresentatives
public import FLT.Mazur.IteratedOldTargetStages
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

universe u v w e h

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  (s b : ∀ i, Finset (I i))
  {J : ι → Type w} [∀ i, Finite (J i)]
  (d : ∀ i, J i → FiniteRelationLocalization.Stage (I i) (r i) (s i))
  {E : ι → ι → Type e} [∀ i j, Finite (E i j)]
  {H : ∀ (_ : ι) j, J j → Type h} [∀ i j k, Finite (H i j k)]

/-- Cofinal shared refinements preserve both old arrow levels with literal coordinate targets. -/
theorem exists_iterated_old_diagram_refinement
    (F : ∀ i j, E i j →
      FiniteRelationLocalization.Quotient (I i) (r i) →ₐ[R]
        FiniteRelationLocalization.Quotient (I j) (r j))
    (G : ∀ i j k, H i j k →
      FiniteRelationLocalization.Quotient (I i) (r i) →ₐ[R]
        FiniteRelationIterated.Quotient R (I j) (r j) (s j) (d j k))
    (Fₛ : ∀ i j, E i j →
      FiniteRelationLocalization.Stage (I i) (r i) (s i) →ₐ[R]
        FiniteRelationLocalization.Stage (I j) (r j) (s j))
    (Gₛ : ∀ i j k, H i j k →
      FiniteRelationLocalization.Stage (I i) (r i) (s i) →ₐ[R]
        FiniteRelationIterated.Stage R (I j) (r j) (s j) (d j k) ⟨s j, le_refl (s j)⟩)
    (hFₛ : ∀ i j a, (FiniteRelationLocalization.toQuotient R (I j) (r j) (s j)).comp
      (Fₛ i j a) = (F i j a).comp
        (FiniteRelationLocalization.toQuotient R (I i) (r i) (s i)))
    (hGₛ : ∀ i j k a, (FiniteRelationIterated.toQuotient R (I j) (r j) (s j) (d j k)
      ⟨s j, le_refl (s j)⟩).comp (Gₛ i j k a) = (G i j k a).comp
        (FiniteRelationLocalization.toQuotient R (I i) (r i) (s i))) :
    ∃ (t : ∀ i, Finset (I i)) (hst : s ≤ t), b ≤ t ∧
      ∃ (Fₜ : ∀ i j, E i j →
          FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
            FiniteRelationLocalization.Stage (I j) (r j) (t j))
        (Gₜ : ∀ i j k, H i j k →
          FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
            FiniteRelationIterated.Stage R (I j) (r j) (s j) (d j k) ⟨t j, hst j⟩),
        (∀ i j a, (Fₜ i j a).comp
          (FiniteRelationLocalization.transition R (I i) (r i) (hst i)) =
            (FiniteRelationLocalization.transition R (I j) (r j) (hst j)).comp (Fₛ i j a)) ∧
        (∀ i j k a, (Gₜ i j k a).comp
          (FiniteRelationLocalization.transition R (I i) (r i) (hst i)) =
            (FiniteRelationIterated.transition R (I j) (r j) (s j) (d j k)
              (show (⟨s j, le_refl (s j)⟩ : Set.Ici (s j)) ≤ ⟨t j, hst j⟩ from hst j)).comp
                (Gₛ i j k a)) ∧
        (∀ i j a, (FiniteRelationLocalization.toQuotient R (I j) (r j) (t j)).comp
          (Fₜ i j a) = (F i j a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i))) ∧
        ∀ i j k a, (FiniteRelationIterated.toQuotient R (I j) (r j) (s j) (d j k)
          ⟨t j, hst j⟩).comp (Gₜ i j k a) = (G i j k a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)) := by
  classical
  obtain ⟨f, g, hfOld, hfFull, hf, hgOld, hgFull, hg, v, w, hv, hw⟩ :=
    exists_iterated_old_diagram_representatives n r I s d F G Fₛ Gₛ hFₛ hGₛ
  obtain ⟨t, hst, hbt, Fₜ, Gₜ, hFₜ, hGₜ⟩ :=
    exists_iterated_old_target_stages n r I s b d f g hf hg v hv w hw
  refine ⟨t, hst, hbt, Fₜ, Gₜ, ?_, ?_, ?_, ?_⟩
  · intro i j a
    exact principal_old_square_of_representatives
      (s := s i) (t := t i) (b := s j) (c := t j) (I i) (r i) (I j) (r j) (hst i) (hst j)
      (f i j a) (Fₛ i j a) (Fₜ i j a) (hfOld i j a) (hFₜ i j a)
  · intro i j k a
    exact old_square_of_representatives
      (s := s i) (t := t i) (c := ⟨s j, le_refl (s j)⟩) (e := ⟨t j, hst j⟩)
      (I i) (r i) (I j) (r j) (s j) (d j k) (hst i)
      (show (⟨s j, le_refl (s j)⟩ : Set.Ici (s j)) ≤ ⟨t j, hst j⟩ from hst j)
      (g i j k a) (Gₛ i j k a) (Gₜ i j k a) (hgOld i j k a) (hGₜ i j k a)
  · intro i j a
    exact principal_recovery_of_representatives (t := t i) (c := t j) (I i) (r i) (I j) (r j)
      (f i j a) (F i j a) (Fₜ i j a) (hfFull i j a) (hFₜ i j a)
  · intro i j k a
    exact recovery_of_representatives (t := t i) (e := ⟨t j, hst j⟩)
      (I i) (r i) (I j) (r j) (s j) (d j k)
      (g i j k a) (G i j k a) (Gₜ i j k a) (hgFull i j k a) (hGₜ i j k a)

end FLT.Mazur.FinitePolynomialCoefficients
