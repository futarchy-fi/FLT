/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedPolynomialStableStages
public import FLT.Mazur.PrincipalQuotientRepresentatives
public import FLT.Mazur.FiniteRelationPrincipalProjection

/-!
# Simultaneous finite stages of original principal-open diagrams

Construct every original arrow at one shared ambient relation stage per vertex.
Both source and target are the canonical principal localizations of those
stages, and every constructed arrow recovers its entire original algebra map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
  {E : ι → ι → Type w} [∀ i j, Finite (E i j)]

/-- Polynomial and inverse representatives give shared stages retaining their numerator formulas. -/
theorem exists_principal_stages_of_representatives
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (hf : ∀ i j e, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
      (f i j e).toRingHom)
    (v : ∀ i j, E i j → Localization.Away (r j))
    (hv : ∀ i j e, f i j e (r i) * v i j e - 1 ∈
      (I j).map (algebraMap _ (Localization.Away (r j))))
    (s : ∀ i, Finset (I i)) :
    ∃ t : ∀ i, Finset (I i), s ≤ t ∧
      ∃ G : ∀ i j, E i j →
        FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
          FiniteRelationLocalization.Stage (I j) (r j) (t j),
        ∀ i j e p, G i j e (algebraMap _ _
          (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)) =
          PrincipalQuotientProjection.projection
            (FiniteRelationModel.relations (I j) (t j)) (r j) (f i j e p) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i j) := Fintype.ofFinite (E i j)
  let K (j) := Σ i, E i j
  let _ (j) : Fintype (K j) := inferInstanceAs (Fintype (Σ i, E i j))
  let x : ∀ j, K j → Localization.Away (r j) :=
    fun _ ⟨i, e⟩ ↦ f i _ e (r i) * v i _ e - 1
  obtain ⟨t, hst, hft, hxt⟩ := exists_localized_stable_stages n r f I hf s x
    (fun _ ⟨i, e⟩ ↦ hv i _ e)
  let G (i j) (e : E i j) := PrincipalQuotientProjection.principalArrowAlgHom R
    (FiniteRelationModel.relations (I j) (t j)) (r j)
    (FiniteRelationModel.relations (I i) (t i)) (r i)
    (f i j e) (hft i j e) (v i j e) (hxt j ⟨i, e⟩)
  exact ⟨t, hst, G, fun i j e p ↦
    PrincipalQuotientProjection.principalArrowAlgHom_numerator R _ _ _ _ _ _ _ _ p⟩

/-- Original principal-open diagrams descend to shared cofinal canonical principal stages. -/
theorem exists_principal_diagram_stages
    (F : ∀ i j, E i j →
      FiniteRelationLocalization.Quotient (I i) (r i) →ₐ[R]
        FiniteRelationLocalization.Quotient (I j) (r j))
    (s : ∀ i, Finset (I i)) :
    ∃ t : ∀ i, Finset (I i), s ≤ t ∧
      ∃ G : ∀ i j, E i j →
        FiniteRelationLocalization.Stage (I i) (r i) (t i) →ₐ[R]
          FiniteRelationLocalization.Stage (I j) (r j) (t j),
        ∀ i j e, (FiniteRelationLocalization.toQuotient R (I j) (r j) (t j)).comp
            (G i j e) =
          (F i j e).comp (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)) := by
  choose f hfac hf v hv using fun i j e ↦
    PrincipalQuotientProjection.exists_representatives (n i) (I i) (r i)
      (I j) (r j) (F i j e)
  obtain ⟨t, hst, G, hG⟩ := exists_principal_stages_of_representatives n r I f hf v hv s
  refine ⟨t, hst, G, fun i j e ↦ ?_⟩
  apply AlgHom.coe_ringHom_injective
  apply PrincipalQuotientProjection.hom_ext
    (FiniteRelationModel.relations (I i) (t i)) (r i)
  intro p
  change FiniteRelationLocalization.toQuotient R (I j) (r j) (t j)
      (G i j e (algebraMap _ _
        (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p))) =
    F i j e (FiniteRelationLocalization.toQuotient R (I i) (r i) (t i)
      (algebraMap _ _
        (Ideal.Quotient.mk (FiniteRelationModel.relations (I i) (t i)) p)))
  rw [hG, FiniteRelationLocalization.toQuotient_projection,
    FiniteRelationLocalization.toQuotient_algebraMap]
  exact hfac i j e p

end FLT.Mazur.FinitePolynomialCoefficients
