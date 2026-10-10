/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OccurrenceQuotientInverseStages
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

/-- Shared stages carry both arrow levels with literal old-denominator numerator formulas. -/
theorem exists_occurrence_old_target_stages
    (f : ∀ i j o, E i j o → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j o))
    (g : ∀ i j o k, H i j o k → MvPolynomial (Fin (n i)) R →ₐ[R]
      Localization.Away (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k)))
    (hf : ∀ i j o a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j o)))).comap
      (f i j o a).toRingHom)
    (hg : ∀ i j o k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j o)))).map
      (algebraMap _ (Localization.Away
        (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k))))).comap
          (g i j o k a).toRingHom)
    (v : ∀ i j o, E i j o → Localization.Away (r j o))
    (hv : ∀ i j o a, f i j o a (r i (src i j o a)) * v i j o a - 1 ∈
      (I j).map (algebraMap _ (Localization.Away (r j o))))
    (w : ∀ i j o k, H i j o k →
      Localization.Away (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k)))
    (hw : ∀ i j o k a, g i j o k a (r i (src₂ i j o k a)) * w i j o k a - 1 ∈
      ((I j).map (algebraMap _ (Localization.Away (r j o)))).map
        (algebraMap _ (Localization.Away
          (oldDenominatorRepresentative (I j) (r j o) (s j) (d j o k))))) :
    ∃ (t : ∀ i, Finset (I i)) (hst : s ≤ t), b ≤ t ∧
      ∃ (Fₜ : ∀ i j o (a : E i j o),
          FiniteRelationLocalization.Stage (I i) (r i (src i j o a)) (t i) →ₐ[R]
            FiniteRelationLocalization.Stage (I j) (r j o) (t j))
        (Gₜ : ∀ i j o k (a : H i j o k),
          FiniteRelationLocalization.Stage (I i) (r i (src₂ i j o k a)) (t i) →ₐ[R]
            FiniteRelationIterated.Stage R (I j) (r j o) (s j) (d j o k) ⟨t j, hst j⟩),
        (∀ i j o a p, Fₜ i j o a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          PrincipalQuotientProjection.projection
            (FiniteRelationModel.relations (I j) (t j)) (r j o) (f i j o a p)) ∧
        ∀ i j o k a p, Gₜ i j o k a (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          oldDenominatorProjection R (I j) (r j o) (s j) (d j o k) ⟨t j, hst j⟩
            (g i j o k a p) := by
  classical
  let q (i o) (k : J i o) := oldDenominatorRepresentative (I i) (r i o) (s i) (d i o k)
  obtain ⟨t, ht, Fₜ, G₀, hFₜ, hG₀, _, _⟩ :=
    exists_occurrence_stages_with_inverse_data n r q I src src₂ f g hf hg v hv w hw
      (fun i ↦ s i ∪ b i) (fun _ _ (k : Empty) ↦ k.elim) (fun _ _ k ↦ k.elim)
      (fun _ _ _ (k : Empty) ↦ k.elim) (fun _ _ _ k ↦ k.elim)
  have hst : s ≤ t := fun i ↦ Finset.subset_union_left.trans (ht i)
  let Gₜ (i j o k) (a : H i j o k) :
      FiniteRelationLocalization.Stage (I i) (r i (src₂ i j o k a)) (t i) →ₐ[R]
        FiniteRelationIterated.Stage R (I j) (r j o) (s j) (d j o k) ⟨t j, hst j⟩ :=
    (oldDenominatorEquiv R (I j) (r j o) (s j) (d j o k) ⟨t j, hst j⟩).toAlgHom.comp (G₀ i j o k a)
  refine ⟨t, hst, fun i ↦ Finset.subset_union_right.trans (ht i), Fₜ, Gₜ, hFₜ, ?_⟩
  intro i j o k a p
  exact equiv_numerator_of_representatives (t := t i) (e := ⟨t j, hst j⟩)
    (I i) (r i (src₂ i j o k a)) (I j) (r j o) (s j) (d j o k)
    (g i j o k a) (G₀ i j o k a) (hG₀ i j o k a) p

end FLT.Mazur.FinitePolynomialCoefficients
