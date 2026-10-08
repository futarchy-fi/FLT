/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedPolynomialStableRelations
public import FLT.Mazur.FiniteRelationIdealRealization

/-!
# Cofinal relation stages for iterated principal diagrams

Realize all arrow and equation closures by one finite relation set per ambient
vertex, simultaneously extending any prescribed initial stages.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z t e h

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {J : ι → Type w} [∀ i, Finite (J i)]
  (s : ∀ i, J i → Localization.Away (r i))
  {K : ι → Type z} [∀ i, Finite (K i)]
  {L : ∀ i, J i → Type t} [∀ i j, Finite (L i j)]
  {E : ι → ι → Type e} [∀ i j, Finite (E i j)]
  {H : ∀ (_ : ι) j, J j → Type h} [∀ i j k, Finite (H i j k)]

/-- Impose both levels of diagram relations at shared cofinal ambient stages. -/
theorem exists_iterated_stable_stages
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (g : ∀ i j k, H i j k →
      MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (s j k))
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ i j a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
      (f i j a).toRingHom)
    (hg : ∀ i j k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j)))).map
      (algebraMap _ (Localization.Away (s j k)))).comap (g i j k a).toRingHom)
    (b : ∀ i, Finset (I i))
    (x : ∀ i, K i → Localization.Away (r i))
    (hx : ∀ i k, x i k ∈ (I i).map (algebraMap _ (Localization.Away (r i))))
    (y : ∀ i j, L i j → Localization.Away (s i j))
    (hy : ∀ i j k, y i j k ∈ ((I i).map (algebraMap _ (Localization.Away (r i)))).map
      (algebraMap _ (Localization.Away (s i j)))) :
    ∃ t : ∀ i, Finset (I i), b ≤ t ∧
      (∀ i j a, FiniteRelationModel.relations (I i) (t i) ≤
        ((FiniteRelationModel.relations (I j) (t j)).map
          (algebraMap _ (Localization.Away (r j)))).comap
        (f i j a).toRingHom) ∧
      (∀ i j k a, FiniteRelationModel.relations (I i) (t i) ≤
        (((FiniteRelationModel.relations (I j) (t j)).map
          (algebraMap _ (Localization.Away (r j)))).map
        (algebraMap _ (Localization.Away (s j k)))).comap (g i j k a).toRingHom) ∧
      (∀ i k, x i k ∈ (FiniteRelationModel.relations (I i) (t i)).map
        (algebraMap _ (Localization.Away (r i)))) ∧
      ∀ i j k, y i j k ∈ ((FiniteRelationModel.relations (I i) (t i)).map
        (algebraMap _ (Localization.Away (r i)))).map
        (algebraMap _ (Localization.Away (s i j))) := by
  classical
  let seed (i) := (b i).image Subtype.val
  have hseed (i) : (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact a.property
  obtain ⟨Q, hfg, hseedQ, hQI, hfQ, hgQ, hxQ, hyQ⟩ :=
    exists_iterated_stable_relations n r s f g I hf hg seed hseed x hx y hy
  have hle (i) : FiniteRelationModel.relations (I i) (b i) ≤ Q i := by
    simpa only [FiniteRelationModel.relations, seed, Finset.coe_image] using hseedQ i
  choose t ht hQ using fun i ↦
    FiniteRelationModel.exists_relations_eq (I i) (b i) (Q i) (hfg i) (hle i) (hQI i)
  exact ⟨t, ht, fun i j a ↦ by rw [hQ, hQ]; exact hfQ i j a,
    fun i j k a ↦ by rw [hQ, hQ]; exact hgQ i j k a,
    fun i k ↦ by rw [hQ]; exact hxQ i k,
    fun i j k ↦ by rw [hQ]; exact hyQ i j k⟩

end FLT.Mazur.FinitePolynomialCoefficients
