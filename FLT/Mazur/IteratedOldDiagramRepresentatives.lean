/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedOldArrowRepresentatives
public import FLT.Mazur.PrincipalOldArrowRepresentatives

/-!
# Simultaneous representatives of old principal and double-open arrows

Choose one representative family for both levels of an actual old diagram.
The denominator representatives remain fixed; the old and original numerator
formulas hold simultaneously and imply preservation of the full ambient ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

open IteratedQuotientProjection

attribute [local irreducible] oldDenominatorEquiv oldDenominatorProjection
  oldDenominatorOriginalProjection oldDenominatorRepresentative

universe u v w e h

variable {R : Type u} [CommRing R] {ι : Type v}
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  (s : ∀ i, Finset (I i))
  {J : ι → Type w}
  (d : ∀ i, J i → FiniteRelationLocalization.Stage (I i) (r i) (s i))
  {E : ι → ι → Type e}
  {H : ∀ (_ : ι) j, J j → Type h}

/-- Simultaneous representatives retain both old levels and both original recovery formulas. -/
theorem exists_iterated_old_diagram_representatives
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
    ∃ (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
      (g : ∀ i j k, H i j k → MvPolynomial (Fin (n i)) R →ₐ[R]
        Localization.Away (oldDenominatorRepresentative (I j) (r j) (s j) (d j k))),
      (∀ i j a p, PrincipalQuotientProjection.projection
        (FiniteRelationModel.relations (I j) (s j)) (r j) (f i j a p) =
          Fₛ i j a (algebraMap _ _
            (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (s i)) p))) ∧
      (∀ i j a p, PrincipalQuotientProjection.projection (I j) (r j) (f i j a p) =
        F i j a (algebraMap _ _ (Ideal.Quotient.mk (I i) p))) ∧
      (∀ i j a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
        (f i j a).toRingHom) ∧
      (∀ i j k a p, oldDenominatorProjection R (I j) (r j) (s j) (d j k)
        ⟨s j, le_refl (s j)⟩ (g i j k a p) = Gₛ i j k a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (s i)) p))) ∧
      (∀ i j k a p, oldDenominatorOriginalProjection R (I j) (r j) (s j) (d j k)
        (g i j k a p) = G i j k a (algebraMap _ _ (Ideal.Quotient.mk (I i) p))) ∧
      (∀ i j k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j)))).map
        (algebraMap _ (Localization.Away
          (oldDenominatorRepresentative (I j) (r j) (s j) (d j k))))).comap
            (g i j k a).toRingHom) ∧
      ∃ (v : ∀ i j, E i j → Localization.Away (r j))
        (w : ∀ i j k, H i j k → Localization.Away
          (oldDenominatorRepresentative (I j) (r j) (s j) (d j k))),
        (∀ i j a, f i j a (r i) * v i j a - 1 ∈
          (I j).map (algebraMap _ (Localization.Away (r j)))) ∧
        ∀ i j k a, g i j k a (r i) * w i j k a - 1 ∈
          ((I j).map (algebraMap _ (Localization.Away (r j)))).map
            (algebraMap _ (Localization.Away
              (oldDenominatorRepresentative (I j) (r j) (s j) (d j k)))) := by
  classical
  choose f hfOld hfFull hf v hv using fun i j a ↦
    PrincipalQuotientProjection.exists_old_representatives (n i) (I i) (r i) (s i)
      (I j) (r j) (s j) (F i j a) (Fₛ i j a) (hFₛ i j a)
  choose g hgOld hgFull hg w hw using fun i j k a ↦
    IteratedQuotientProjection.exists_old_representatives (n i) (I i) (r i) (s i)
      (I j) (r j) (s j) (d j k) ⟨s j, le_refl (s j)⟩ (G i j k a) (Gₛ i j k a) (hGₛ i j k a)
  exact ⟨f, g, hfOld, hfFull, hf, hgOld, hgFull, hg, v, w, hv, hw⟩

end FLT.Mazur.FinitePolynomialCoefficients
