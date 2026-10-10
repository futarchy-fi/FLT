/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedPolynomialDiagramCoefficients
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Simultaneous finite closure with canonical localized targets

Choose one finite ambient ideal per vertex. Every polynomial-to-principal
arrow preserves these ideals, and every prescribed localized relation survives.
The localized target ideal is the image of that same ambient ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {E : ι → ι → Type w} [∀ i j, Finite (E i j)]
  {K : ι → Type z} [∀ i, Finite (K i)]

/-- Close all localized arrows and seed equations at one finite ideal per ambient vertex. -/
theorem exists_localized_stable_relations
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ i j e, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
      (f i j e).toRingHom)
    (seed : ∀ i, Finset (MvPolynomial (Fin (n i)) R))
    (hs : ∀ i, (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i)
    (x : ∀ i, K i → Localization.Away (r i))
    (hx : ∀ i k, x i k ∈ (I i).map (algebraMap _ (Localization.Away (r i)))) :
    ∃ J : ∀ i, Ideal (MvPolynomial (Fin (n i)) R),
      (∀ i, (J i).FG) ∧ (∀ i, Ideal.span (seed i : Set _) ≤ J i) ∧
      (∀ i, J i ≤ I i) ∧
      (∀ i j e, J i ≤ ((J j).map (algebraMap _ (Localization.Away (r j)))).comap
        (f i j e).toRingHom) ∧
      ∀ i k, x i k ∈ (J i).map (algebraMap _ (Localization.Away (r i))) := by
  obtain ⟨S, hS, hsS, r₀, hr, d, hd, _, hxS, f₀, hf₀⟩ :=
    exists_localized_diagram_coefficients n r f x seed
  let _ := hS
  let c (i) := MvPolynomial.map (σ := Fin (n i)) S.subtype
  let J (i) := NoetherianRelationContraction.relations (c i) (I i)
  have hloc (i) : NoetherianRelationContraction.relations (d i)
      ((I i).map (algebraMap _ (Localization.Away (r i)))) =
      (J i).map (algebraMap _ (Localization.Away (r i))) := by
    apply NoetherianRelationContraction.relations_localization
      (Submonoid.powers (r₀ i)) (Submonoid.powers (r i)) (c i) (d i) (hd i)
    rw [Submonoid.map_powers, hr]
  refine ⟨J, fun i ↦ NoetherianRelationContraction.relations_fg (c i) (I i),
    fun i ↦ NoetherianRelationContraction.span_le_relations (c i) (I i) _ (hs i) (hsS i),
    fun i ↦ NoetherianRelationContraction.relations_le (c i) (I i), ?_, ?_⟩
  · intro i j e
    apply Ideal.map_le_iff_le_comap.mp
    rw [← hloc j]
    exact NoetherianRelationContraction.map_relations_le (c i) (I i) (d j)
      ((I j).map (algebraMap _ (Localization.Away (r j))))
      (f i j e).toRingHom (f₀ i j e).toRingHom (hf₀ i j e) (hf i j e)
  · intro i k
    obtain ⟨y, hy⟩ := hxS i k
    rw [← hloc i, ← hy]
    exact NoetherianRelationContraction.mem_relations (d i)
      ((I i).map (algebraMap _ (Localization.Away (r i)))) (hy ▸ hx i k)

end FLT.Mazur.FinitePolynomialCoefficients
