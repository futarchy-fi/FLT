/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OccurrenceDiagramCoefficients
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Shared ambient relation ideals for all occurrences

Include arbitrary auxiliary fractions in the same coefficient construction as
all occurrence arrows and equations. In particular, chosen inverse representatives can
be retained before the shared ambient ideal is contracted.
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

/-- Close the diagram with auxiliary fractions included in its common coefficient ring. -/
theorem exists_occurrence_stable_relations_with_data
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
    (seed : ∀ i, Finset (MvPolynomial (Fin (n i)) R))
    (hseed : ∀ i, (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆ I i)
    (x : ∀ i o, K i o → Localization.Away (r i o))
    (hx : ∀ i o k, x i o k ∈ (I i).map (algebraMap _ (Localization.Away (r i o))))
    (y : ∀ i o j, L i o j → Localization.Away (s i o j))
    (hy : ∀ i o j k, y i o j k ∈ ((I i).map (algebraMap _ (Localization.Away (r i o)))).map
      (algebraMap _ (Localization.Away (s i o j)))) :
    ∃ Q : ∀ i, Ideal (MvPolynomial (Fin (n i)) R),
      (∀ i, (Q i).FG) ∧ (∀ i, Ideal.span (seed i : Set _) ≤ Q i) ∧
      (∀ i, Q i ≤ I i) ∧
      (∀ i j o a, Q i ≤ ((Q j).map (algebraMap _ (Localization.Away (r j o)))).comap
        (f i j o a).toRingHom) ∧
      (∀ i j o k a, Q i ≤ (((Q j).map (algebraMap _ (Localization.Away (r j o)))).map
        (algebraMap _ (Localization.Away (s j o k)))).comap (g i j o k a).toRingHom) ∧
      (∀ i o k, x i o k ∈ (Q i).map (algebraMap _ (Localization.Away (r i o)))) ∧
      ∀ i o j k, y i o j k ∈ ((Q i).map (algebraMap _ (Localization.Away (r i o)))).map
        (algebraMap _ (Localization.Away (s i o j))) := by
  classical
  let _ (i o) := Fintype.ofFinite (K i o)
  let _ (i o j) := Fintype.ofFinite (L i o j)
  let _ (i o) := Fintype.ofFinite (A i o)
  let _ (i o j) := Fintype.ofFinite (B i o j)
  let x' (i o) : K i o ⊕ A i o → Localization.Away (r i o) := Sum.elim (x i o) (z i o)
  let y' (i o j) : L i o j ⊕ B i o j → Localization.Away (s i o j) := Sum.elim (y i o j) (w i o j)
  obtain ⟨S, hS, hseedS, r₀, hr, d, hd, _, hxS, s₀, hs, e, he, _, hyS,
    ⟨f₀, hf₀⟩, g₀, hg₀⟩ := exists_occurrence_diagram_coefficients n r s f g x' y' seed
  let _ := hS
  let c (i) := MvPolynomial.map (σ := Fin (n i)) S.subtype
  let Q (i) := NoetherianRelationContraction.relations (c i) (I i)
  have hloc (i o) : NoetherianRelationContraction.relations (d i o)
      ((I i).map (algebraMap _ (Localization.Away (r i o)))) =
      (Q i).map (algebraMap _ (Localization.Away (r i o))) := by
    apply NoetherianRelationContraction.relations_localization
      (Submonoid.powers (r₀ i o)) (Submonoid.powers (r i o)) (c i) (d i o) (hd i o)
    rw [Submonoid.map_powers, hr]
  have hiter (i o j) : NoetherianRelationContraction.relations (e i o j)
      (((I i).map (algebraMap _ (Localization.Away (r i o)))).map
        (algebraMap _ (Localization.Away (s i o j)))) =
      ((Q i).map (algebraMap _ (Localization.Away (r i o)))).map
        (algebraMap _ (Localization.Away (s i o j))) := by
    rw [← hloc i o]
    apply NoetherianRelationContraction.relations_localization
      (Submonoid.powers (s₀ i o j)) (Submonoid.powers (s i o j)) (d i o) (e i o j) (he i o j)
    rw [Submonoid.map_powers, hs]
  refine ⟨Q, fun i ↦ NoetherianRelationContraction.relations_fg (c i) (I i),
    fun i ↦ NoetherianRelationContraction.span_le_relations (c i) (I i) _
      (hseed i) (hseedS i),
    fun i ↦ NoetherianRelationContraction.relations_le (c i) (I i), ?_, ?_, ?_, ?_⟩
  · intro i j o a
    apply Ideal.map_le_iff_le_comap.mp
    rw [← hloc j o]
    exact NoetherianRelationContraction.map_relations_le (c i) (I i) (d j o)
      ((I j).map (algebraMap _ (Localization.Away (r j o))))
      (f i j o a).toRingHom (f₀ i j o a).toRingHom (hf₀ i j o a) (hf i j o a)
  · intro i j o k a
    apply Ideal.map_le_iff_le_comap.mp
    rw [← hiter j o k]
    exact NoetherianRelationContraction.map_relations_le (c i) (I i) (e j o k)
      (((I j).map (algebraMap _ (Localization.Away (r j o)))).map
        (algebraMap _ (Localization.Away (s j o k))))
      (g i j o k a).toRingHom (g₀ i j o k a).toRingHom (hg₀ i j o k a) (hg i j o k a)
  · intro i o k
    obtain ⟨z, hz⟩ := hxS i o (.inl k)
    change d i o z = x i o k at hz
    rw [← hloc i o, ← hz]
    exact NoetherianRelationContraction.mem_relations (d i o) _ (hz ▸ hx i o k)
  · intro i o j k
    obtain ⟨z, hz⟩ := hyS i o j (.inl k)
    change e i o j z = y i o j k at hz
    rw [← hiter i o j, ← hz]
    exact NoetherianRelationContraction.mem_relations (e i o j) _ (hz ▸ hy i o j k)

end FLT.Mazur.FinitePolynomialCoefficients
