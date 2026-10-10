/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientInverseDataStages
public import FLT.Mazur.IteratedRefinementSquareCriteria

/-!
# Shared quotient stages with literal old-denominator targets

Construct arrows from polynomial representatives and inverse data, then
transport every iterated target to the literal old-coordinate localization.
Both arrow levels retain their full numerator formulas at the same stages.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

open IteratedQuotientProjection

attribute [local irreducible] oldDenominatorEquiv oldDenominatorProjection
  oldDenominatorRepresentative

universe u v w e h

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  (s b : ∀ i, Finset (I i))
  {J : ι → Type w} [∀ i, Finite (J i)]
  (d : ∀ i, J i → FiniteRelationLocalization.Stage (I i) (r i) (s i))
  {E : ι → ι → Type e} [∀ i j, Finite (E i j)]
  {H : ∀ (_ : ι) j, J j → Type h} [∀ i j k, Finite (H i j k)]

/-- Shared stages carry both arrow levels with literal old-denominator numerator formulas. -/
theorem exists_iterated_old_target_stages
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (g : ∀ i j k, H i j k → MvPolynomial (Fin (n i)) R →ₐ[R]
      Localization.Away (oldDenominatorRepresentative (I j) (r j) (s j) (d j k)))
    (hf : ∀ i j a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
      (f i j a).toRingHom)
    (hg : ∀ i j k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j)))).map
      (algebraMap _ (Localization.Away
        (oldDenominatorRepresentative (I j) (r j) (s j) (d j k))))).comap (g i j k a).toRingHom)
    (v : ∀ i j, E i j → Localization.Away (r j))
    (hv : ∀ i j a, f i j a (r i) * v i j a - 1 ∈
      (I j).map (algebraMap _ (Localization.Away (r j))))
    (w : ∀ i j k, H i j k →
      Localization.Away (oldDenominatorRepresentative (I j) (r j) (s j) (d j k)))
    (hw : ∀ i j k a, g i j k a (r i) * w i j k a - 1 ∈
      ((I j).map (algebraMap _ (Localization.Away (r j)))).map
        (algebraMap _ (Localization.Away
          (oldDenominatorRepresentative (I j) (r j) (s j) (d j k))))) :
    ∃ (t : ∀ i, Finset (I i)) (hst : s ≤ t), b ≤ t ∧
      ∃ (Fₜ : ∀ i j, E i j →
          FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
            FiniteRelationLocalization.Stage (I j) (r j) (t j))
        (Gₜ : ∀ i j k, H i j k →
          FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
            FiniteRelationIterated.Stage R (I j) (r j) (s j) (d j k) ⟨t j, hst j⟩),
        (∀ i j a p, Fₜ i j a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          PrincipalQuotientProjection.projection
            (FiniteRelationModel.relations (I j) (t j)) (r j) (f i j a p)) ∧
        ∀ i j k a p, Gₜ i j k a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          oldDenominatorProjection R (I j) (r j) (s j) (d j k) ⟨t j, hst j⟩ (g i j k a p) := by
  classical
  let q (i) (k : J i) := oldDenominatorRepresentative (I i) (r i) (s i) (d i k)
  obtain ⟨t, ht, Fₜ, G₀, hFₜ, hG₀, _, _⟩ :=
    exists_iterated_stages_with_inverse_data n r q I f g hf hg v hv w hw
      (fun i ↦ s i ∪ b i) (fun _ (k : Empty) ↦ k.elim) (fun _ k ↦ k.elim)
      (fun _ _ (k : Empty) ↦ k.elim) (fun _ _ k ↦ k.elim)
  have hst : s ≤ t := fun i ↦ Finset.subset_union_left.trans (ht i)
  let Gₜ (i j k) (a : H i j k) :
      FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
        FiniteRelationIterated.Stage R (I j) (r j) (s j) (d j k) ⟨t j, hst j⟩ :=
    (oldDenominatorEquiv R (I j) (r j) (s j) (d j k) ⟨t j, hst j⟩).toAlgHom.comp (G₀ i j k a)
  refine ⟨t, hst, fun i ↦ Finset.subset_union_right.trans (ht i), Fₜ, Gₜ, hFₜ, ?_⟩
  intro i j k a p
  exact equiv_numerator_of_representatives (t := t i) (e := ⟨t j, hst j⟩)
    (I i) (r i) (I j) (r j) (s j) (d j k)
    (g i j k a) (G₀ i j k a) (hG₀ i j k a) p

end FLT.Mazur.FinitePolynomialCoefficients
