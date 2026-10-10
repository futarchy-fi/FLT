/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedQuotientDiagramStages
public import FLT.Mazur.IteratedQuotientRepresentatives
public import FLT.Mazur.IteratedQuotientRecovery
public import FLT.Mazur.PrincipalQuotientRepresentatives

/-!
# Original diagrams on shared iterated principal stages

Starting from actual original principal and double-open arrows, construct their
finite-stage arrows together. The original recovery squares hold on full rings,
not just on selected generators.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z e h

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {J : ι → Type w} [∀ i, Finite (J i)]
  (s : ∀ i, J i → Localization.Away (r i))
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  {E : ι → ι → Type e} [∀ i j, Finite (E i j)]
  {H : ∀ (_ : ι) j, J j → Type h} [∀ i j k, Finite (H i j k)]

/-- Actual original arrows descend to shared cofinal principal and iterated quotient stages. -/
theorem exists_iterated_diagram_stages
    (F : ∀ i j, E i j →
      PrincipalQuotientProjection.Target (I i) (r i) →ₐ[R]
        PrincipalQuotientProjection.Target (I j) (r j))
    (G : ∀ i j k, H i j k →
      PrincipalQuotientProjection.Target (I i) (r i) →ₐ[R]
        IteratedQuotientProjection.Target (I j) (r j) (s j k))
    (b : ∀ i, Finset (I i)) :
    ∃ t : ∀ i, Finset (I i), b ≤ t ∧
      ∃ (F₀ : ∀ i j, E i j →
          FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
            FiniteRelationLocalization.Stage (I j) (r j) (t j))
        (G₀ : ∀ i j k, H i j k →
          FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
            IteratedQuotientProjection.Target
              (FiniteRelationModel.relations (I j) (t j)) (r j) (s j k)),
        (∀ i j a, (FiniteRelationLocalization.toQuotient R (I j) (r j) (t j)).comp
          (F₀ i j a) = (F i j a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i))) ∧
        ∀ i j k a, (IteratedQuotientProjection.stageToQuotient R (I j) (r j)
          (s j k) (t j)).comp (G₀ i j k a) = (G i j k a).comp
            (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)) := by
  choose f hfac hf v hv using fun i j a ↦
    PrincipalQuotientProjection.exists_representatives (n i) (I i) (r i)
      (I j) (r j) (F i j a)
  choose g hgfac hg w hw using fun i j k a ↦
    IteratedQuotientProjection.exists_representatives (n i) (I i) (r i)
      (I j) (r j) (s j k) (G i j k a)
  obtain ⟨t, ht, F₀, G₀, hF₀, hG₀, _, _⟩ :=
    exists_iterated_stages_of_representatives n r s I f g hf hg v hv w hw b
      (fun _ (k : Empty) ↦ k.elim) (fun _ k ↦ k.elim)
      (fun _ _ (k : Empty) ↦ k.elim) (fun _ _ k ↦ k.elim)
  refine ⟨t, ht, F₀, G₀, ?_, ?_⟩
  · intro i j a
    apply AlgHom.coe_ringHom_injective
    apply PrincipalQuotientProjection.hom_ext
      (FiniteRelationModel.relations (I i) (t i)) (r i)
    intro p
    change FiniteRelationLocalization.toQuotient R (I j) (r j) (t j)
      (F₀ i j a (algebraMap _ _
        (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p))) =
      F i j a (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)
        (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)))
    rw [hF₀, FiniteRelationLocalization.toQuotient_projection,
      FiniteRelationLocalization.toQuotient_algebraMap]
    exact hfac i j a p
  · intro i j k a
    apply AlgHom.coe_ringHom_injective
    apply PrincipalQuotientProjection.hom_ext
      (FiniteRelationModel.relations (I i) (t i)) (r i)
    intro p
    change IteratedQuotientProjection.stageToQuotient R (I j) (r j) (s j k) (t j)
      (G₀ i j k a (algebraMap _ _
        (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p))) =
      G i j k a (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)
        (algebraMap _ _ (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)))
    rw [hG₀, IteratedQuotientProjection.stageToQuotient_projection,
      FiniteRelationLocalization.toQuotient_algebraMap]
    exact hgfac i j k a p

end FLT.Mazur.FinitePolynomialCoefficients
