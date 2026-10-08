/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialStableRelations
public import FLT.Mazur.FiniteRelationIdealRealization

/-!
# Cofinal simultaneous stages for finite polynomial diagrams

Finite stable ideals are realized by the existing finite-relation stage
format. Each vertex has just one stage, used by both its incoming and its
outgoing arrows. All old relations are retained.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {E : Type w} [Finite E] (n : ι → ℕ) (src dst : E → ι)

/-- All polynomial arrows preserve one cofinal finite relation set per vertex. -/
theorem exists_stable_stages
    (f : ∀ e, MvPolynomial (Fin (n (src e))) R →ₐ[R]
      MvPolynomial (Fin (n (dst e))) R)
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ e, I (src e) ≤ (I (dst e)).comap (f e).toRingHom)
    (s : ∀ i, Finset (I i)) :
    ∃ t : ∀ i, Finset (I i), s ≤ t ∧
      ∀ e, FiniteRelationModel.relations (I (src e)) (t (src e)) ≤
        (FiniteRelationModel.relations (I (dst e)) (t (dst e))).comap (f e).toRingHom := by
  classical
  let seed (i) := (s i).image Subtype.val
  have hs (i) : (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact x.property
  obtain ⟨J, hfg, hseed, hJI, hfJ⟩ := exists_stable_relations n src dst f I hf seed hs
  have hle (i) : FiniteRelationModel.relations (I i) (s i) ≤ J i := by
    simpa only [FiniteRelationModel.relations, seed, Finset.coe_image] using hseed i
  choose t ht hJ using fun i ↦
    FiniteRelationModel.exists_relations_eq (I i) (s i) (J i) (hfg i) (hle i) (hJI i)
  exact ⟨t, ht, fun e ↦ by rw [hJ, hJ]; exact hfJ e⟩

end FLT.Mazur.FinitePolynomialCoefficients
