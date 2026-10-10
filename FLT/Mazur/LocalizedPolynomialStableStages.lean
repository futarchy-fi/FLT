/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedPolynomialStableRelations
public import FLT.Mazur.FiniteRelationIdealRealization

/-!
# Shared cofinal relation stages with canonical localized targets

The same finite relation set controls a vertex both as an arrow source and as
a localized target. Localized seed equations, including inverse-coordinate
relations, are imposed without assigning independent double-open ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {E : ι → ι → Type w} [∀ i j, Finite (E i j)]
  {K : ι → Type z} [∀ i, Finite (K i)]

/-- Realize simultaneous localized closure by one cofinal finite relation stage per vertex. -/
theorem exists_localized_stable_stages
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ i j e, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
      (f i j e).toRingHom)
    (s : ∀ i, Finset (I i)) (x : ∀ i, K i → Localization.Away (r i))
    (hx : ∀ i k, x i k ∈ (I i).map (algebraMap _ (Localization.Away (r i)))) :
    ∃ t : ∀ i, Finset (I i), s ≤ t ∧
      (∀ i j e, FiniteRelationModel.relations (I i) (t i) ≤
        ((FiniteRelationModel.relations (I j) (t j)).map
          (algebraMap _ (Localization.Away (r j)))).comap (f i j e).toRingHom) ∧
      ∀ i k, x i k ∈ (FiniteRelationModel.relations (I i) (t i)).map
        (algebraMap _ (Localization.Away (r i))) := by
  classical
  let seed (i) := (s i).image Subtype.val
  have hs (i) : (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    exact y.property
  obtain ⟨J, hfg, hseed, hJI, hfJ, hxJ⟩ :=
    exists_localized_stable_relations n r f I hf seed hs x hx
  have hle (i) : FiniteRelationModel.relations (I i) (s i) ≤ J i := by
    simpa only [FiniteRelationModel.relations, seed, Finset.coe_image] using hseed i
  choose t ht hJ using fun i ↦
    FiniteRelationModel.exists_relations_eq (I i) (s i) (J i) (hfg i) (hle i) (hJI i)
  exact ⟨t, ht, fun i j e ↦ by rw [hJ, hJ]; exact hfJ i j e,
    fun i k ↦ by rw [hJ]; exact hxJ i k⟩

end FLT.Mazur.FinitePolynomialCoefficients
