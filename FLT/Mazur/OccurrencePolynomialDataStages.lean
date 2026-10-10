/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OccurrencePolynomialDataRelations
public import FLT.Mazur.FiniteRelationIdealRealization

/-!
# Cofinal shared ambient stages for all occurrences

Realize a closure that includes arbitrary selected fractions in the common
coefficient construction, using one relation set per ambient vertex, independent of the occurrence.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z t e h z₁ t₁ q

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) {O : ι → Type q} [∀ i, Finite (O i)]
  (r : ∀ i, O i → MvPolynomial (Fin (n i)) R)
  {J : ∀ i, O i → Type w} [∀ i o, Finite (J i o)]
  (s : ∀ i o, J i o → Localization.Away (r i o))
  {K : ∀ i, O i → Type z} [∀ i o, Finite (K i o)]
  {L : ∀ i o, J i o → Type t} [∀ i o j, Finite (L i o j)]
  {A : ∀ i, O i → Type z₁} [∀ i o, Finite (A i o)]
  {B : ∀ i o, J i o → Type t₁} [∀ i o j, Finite (B i o j)]
  {E : ∀ (_ : ι) j, O j → Type e} [∀ i j o, Finite (E i j o)]
  {H : ∀ (_ : ι) j o, J j o → Type h} [∀ i j o k, Finite (H i j o k)]

/-- Impose both levels of diagram relations at shared cofinal ambient stages. -/
theorem exists_occurrence_stable_stages_with_data
    (f : ∀ i j o, E i j o → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j o))
    (g : ∀ i j o k, H i j o k →
      MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (s j o k))
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ i j o a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j o)))).comap
      (f i j o a).toRingHom)
    (hg : ∀ i j o k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j o)))).map
      (algebraMap _ (Localization.Away (s j o k)))).comap (g i j o k a).toRingHom)
    (z : ∀ i o, A i o → Localization.Away (r i o))
    (w : ∀ i o j, B i o j → Localization.Away (s i o j))
    (b : ∀ i, Finset (I i))
    (x : ∀ i o, K i o → Localization.Away (r i o))
    (hx : ∀ i o k, x i o k ∈ (I i).map (algebraMap _ (Localization.Away (r i o))))
    (y : ∀ i o j, L i o j → Localization.Away (s i o j))
    (hy : ∀ i o j k, y i o j k ∈ ((I i).map (algebraMap _ (Localization.Away (r i o)))).map
      (algebraMap _ (Localization.Away (s i o j)))) :
    ∃ t : ∀ i, Finset (I i), b ≤ t ∧
      (∀ i j o a, FiniteRelationModel.relations (I i) (t i) ≤
        ((FiniteRelationModel.relations (I j) (t j)).map
          (algebraMap _ (Localization.Away (r j o)))).comap
        (f i j o a).toRingHom) ∧
      (∀ i j o k a, FiniteRelationModel.relations (I i) (t i) ≤
        (((FiniteRelationModel.relations (I j) (t j)).map
          (algebraMap _ (Localization.Away (r j o)))).map
        (algebraMap _ (Localization.Away (s j o k)))).comap (g i j o k a).toRingHom) ∧
      (∀ i o k, x i o k ∈ (FiniteRelationModel.relations (I i) (t i)).map
        (algebraMap _ (Localization.Away (r i o)))) ∧
      ∀ i o j k, y i o j k ∈ ((FiniteRelationModel.relations (I i) (t i)).map
        (algebraMap _ (Localization.Away (r i o)))).map
        (algebraMap _ (Localization.Away (s i o j))) := by
  classical
  let seed (i) := (b i).image Subtype.val
  have hseed (i) : (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact a.property
  obtain ⟨Q, hfg, hseedQ, hQI, hfQ, hgQ, hxQ, hyQ⟩ :=
    exists_occurrence_stable_relations_with_data n r s f g I hf hg z w seed hseed x hx y hy
  have hle (i) : FiniteRelationModel.relations (I i) (b i) ≤ Q i := by
    simpa only [FiniteRelationModel.relations, seed, Finset.coe_image] using hseedQ i
  choose t ht hQ using fun i ↦
    FiniteRelationModel.exists_relations_eq (I i) (b i) (Q i) (hfg i) (hle i) (hQI i)
  exact ⟨t, ht, fun i j o a ↦ by rw [hQ, hQ]; exact hfQ i j o a,
    fun i j o k a ↦ by rw [hQ, hQ]; exact hgQ i j o k a,
    fun i o k ↦ by rw [hQ]; exact hxQ i o k,
    fun i o j k ↦ by rw [hQ]; exact hyQ i o j k⟩

end FLT.Mazur.FinitePolynomialCoefficients
