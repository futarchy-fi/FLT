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

universe u v w e h q

variable {R : Type u} [CommRing R] {ι : Type v}
  (n : ι → ℕ) {O : ι → Type q}
  (r : ∀ i, O i → MvPolynomial (Fin (n i)) R)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  (s : ∀ i, Finset (I i))
  {J : ∀ i, O i → Type w}
  (d : ∀ i o, J i o → FiniteRelationLocalization.Stage (I i) (r i o) (s i))
  {E : ∀ (_ : ι) j, O j → Type e}
  {H : ∀ (_ : ι) j o, J j o → Type h}
  (src : ∀ i j o, E i j o → O i)
  (src₂ : ∀ i j o k, H i j o k → O i)

/-- Simultaneous representatives retain both old levels and both original recovery formulas. -/
theorem exists_occurrence_old_diagram_representatives
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
    ∃ (f : ∀ i j o, E i j o → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j o))
      (g : ∀ i j o k, H i j o k → MvPolynomial (Fin (n i)) R →ₐ[R]
        Localization.Away (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k))),
      (∀ i j o a p, PrincipalQuotientProjection.projection
        (FiniteRelationModel.relations (I j) (s j)) (r j o) (f i j o a p) =
          Fₛ i j o a (algebraMap _ _
            (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (s i)) p))) ∧
      (∀ i j o a p, PrincipalQuotientProjection.projection (I j) (r j o) (f i j o a p) =
        F i j o a (algebraMap _ _ (Ideal.Quotient.mk (I i) p))) ∧
      (∀ i j o a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j o)))).comap
        (f i j o a).toRingHom) ∧
      (∀ i j o k a p, oldDenominatorProjection R (I j) (r j o) (s j) (d j o k)
        ⟨s j, le_refl (s j)⟩ (g i j o k a p) = Gₛ i j o k a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (s i)) p))) ∧
      (∀ i j o k a p, oldDenominatorOriginalProjection R (I j) (r j o) (s j) (d j o k)
        (g i j o k a p) = G i j o k a (algebraMap _ _ (Ideal.Quotient.mk (I i) p))) ∧
      (∀ i j o k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j o)))).map
        (algebraMap _ (Localization.Away
          (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k))))).comap
            (g i j o k a).toRingHom) ∧
      ∃ (v : ∀ i j o, E i j o → Localization.Away (r j o))
        (w : ∀ i j o k, H i j o k → Localization.Away
          (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k))),
        (∀ i j o a, f i j o a (r i (src i j o a)) * v i j o a - 1 ∈
          (I j).map (algebraMap _ (Localization.Away (r j o)))) ∧
        ∀ i j o k a, g i j o k a (r i (src₂ i j o k a)) * w i j o k a - 1 ∈
          ((I j).map (algebraMap _ (Localization.Away (r j o)))).map
            (algebraMap _ (Localization.Away
              (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k)))) := by
  classical
  choose f hfOld hfFull hf v hv using fun i j o a ↦
    PrincipalQuotientProjection.exists_old_representatives (n i) (I i) (r i (src i j o a)) (s i)
      (I j) (r j o) (s j) (F i j o a) (Fₛ i j o a) (hFₛ i j o a)
  choose g hgOld hgFull hg w hw using fun i j o k a ↦
    IteratedQuotientProjection.exists_old_representatives (n i) (I i) (r i (src₂ i j o k a)) (s i)
      (I j) (r j o) (s j) (d j o k) ⟨s j, le_refl (s j)⟩
      (G i j o k a) (Gₛ i j o k a) (hGₛ i j o k a)
  exact ⟨f, g, hfOld, hfFull, hf, hgOld, hgFull, hg, v, w, hv, hw⟩

end FLT.Mazur.FinitePolynomialCoefficients
