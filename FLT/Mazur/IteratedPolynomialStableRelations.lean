/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IteratedPolynomialDiagramCoefficients
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Shared finite relation ideals on iterated principal diagrams

One finitely generated ideal at each ambient vertex controls both localization
levels, all arrows and all selected equations. No independently chosen ideal
is introduced for a second principal open.
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

/-- Close all arrows and equations using literal extensions of shared ambient finite ideals. -/
theorem exists_iterated_stable_relations
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (g : ∀ i j k, H i j k →
      MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (s j k))
    (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))
    (hf : ∀ i j a, I i ≤ ((I j).map (algebraMap _ (Localization.Away (r j)))).comap
      (f i j a).toRingHom)
    (hg : ∀ i j k a, I i ≤ (((I j).map (algebraMap _ (Localization.Away (r j)))).map
      (algebraMap _ (Localization.Away (s j k)))).comap (g i j k a).toRingHom)
    (seed : ∀ i, Finset (MvPolynomial (Fin (n i)) R))
    (hseed : ∀ i, (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i)
    (x : ∀ i, K i → Localization.Away (r i))
    (hx : ∀ i k, x i k ∈ (I i).map (algebraMap _ (Localization.Away (r i))))
    (y : ∀ i j, L i j → Localization.Away (s i j))
    (hy : ∀ i j k, y i j k ∈ ((I i).map (algebraMap _ (Localization.Away (r i)))).map
      (algebraMap _ (Localization.Away (s i j)))) :
    ∃ Q : ∀ i, Ideal (MvPolynomial (Fin (n i)) R),
      (∀ i, (Q i).FG) ∧ (∀ i, Ideal.span (seed i : Set _) ≤ Q i) ∧
      (∀ i, Q i ≤ I i) ∧
      (∀ i j a, Q i ≤ ((Q j).map (algebraMap _ (Localization.Away (r j)))).comap
        (f i j a).toRingHom) ∧
      (∀ i j k a, Q i ≤ (((Q j).map (algebraMap _ (Localization.Away (r j)))).map
        (algebraMap _ (Localization.Away (s j k)))).comap (g i j k a).toRingHom) ∧
      (∀ i k, x i k ∈ (Q i).map (algebraMap _ (Localization.Away (r i)))) ∧
      ∀ i j k, y i j k ∈ ((Q i).map (algebraMap _ (Localization.Away (r i)))).map
        (algebraMap _ (Localization.Away (s i j))) := by
  obtain ⟨S, hS, hseedS, r₀, hr, d, hd, _, hxS, s₀, hs, e, he, _, hyS,
    ⟨f₀, hf₀⟩, g₀, hg₀⟩ := exists_iterated_diagram_coefficients n r s f g x y seed
  let _ := hS
  let c (i) := MvPolynomial.map (σ := Fin (n i)) S.subtype
  let Q (i) := NoetherianRelationContraction.relations (c i) (I i)
  have hloc (i) : NoetherianRelationContraction.relations (d i)
      ((I i).map (algebraMap _ (Localization.Away (r i)))) =
      (Q i).map (algebraMap _ (Localization.Away (r i))) := by
    apply NoetherianRelationContraction.relations_localization
      (Submonoid.powers (r₀ i)) (Submonoid.powers (r i)) (c i) (d i) (hd i)
    rw [Submonoid.map_powers, hr]
  have hiter (i j) : NoetherianRelationContraction.relations (e i j)
      (((I i).map (algebraMap _ (Localization.Away (r i)))).map
        (algebraMap _ (Localization.Away (s i j)))) =
      ((Q i).map (algebraMap _ (Localization.Away (r i)))).map
        (algebraMap _ (Localization.Away (s i j))) := by
    rw [← hloc i]
    apply NoetherianRelationContraction.relations_localization
      (Submonoid.powers (s₀ i j)) (Submonoid.powers (s i j)) (d i) (e i j) (he i j)
    rw [Submonoid.map_powers, hs]
  refine ⟨Q, fun i ↦ NoetherianRelationContraction.relations_fg (c i) (I i),
    fun i ↦ NoetherianRelationContraction.span_le_relations (c i) (I i) _
      (hseed i) (hseedS i),
    fun i ↦ NoetherianRelationContraction.relations_le (c i) (I i), ?_, ?_, ?_, ?_⟩
  · intro i j a
    apply Ideal.map_le_iff_le_comap.mp
    rw [← hloc j]
    exact NoetherianRelationContraction.map_relations_le (c i) (I i) (d j)
      ((I j).map (algebraMap _ (Localization.Away (r j))))
      (f i j a).toRingHom (f₀ i j a).toRingHom (hf₀ i j a) (hf i j a)
  · intro i j k a
    apply Ideal.map_le_iff_le_comap.mp
    rw [← hiter j k]
    exact NoetherianRelationContraction.map_relations_le (c i) (I i) (e j k)
      (((I j).map (algebraMap _ (Localization.Away (r j)))).map
        (algebraMap _ (Localization.Away (s j k))))
      (g i j k a).toRingHom (g₀ i j k a).toRingHom (hg₀ i j k a) (hg i j k a)
  · intro i k
    obtain ⟨z, hz⟩ := hxS i k
    rw [← hloc i, ← hz]
    exact NoetherianRelationContraction.mem_relations (d i) _ (hz ▸ hx i k)
  · intro i j k
    obtain ⟨z, hz⟩ := hyS i j k
    rw [← hiter i j, ← hz]
    exact NoetherianRelationContraction.mem_relations (e i j) _ (hz ▸ hy i j k)

end FLT.Mazur.FinitePolynomialCoefficients
