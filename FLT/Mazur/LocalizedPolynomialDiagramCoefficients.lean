/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocalizedPolynomialCoefficients

/-!
# Common coefficient squares for polynomial maps into principal opens

All arrows descend simultaneously to genuine localized coefficient targets.
Additional finite fraction data can include inverse coordinates and equations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {E : ι → ι → Type w} [∀ i j, Finite (E i j)]
  {K : ι → Type z} [∀ i, Finite (K i)]

/-- All polynomial-to-principal arrows and extra fractions share one coefficient model. -/
theorem exists_localized_diagram_coefficients
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (x : ∀ i, K i → Localization.Away (r i))
    (seed : ∀ i, Finset (MvPolynomial (Fin (n i)) R)) :
    ∃ S : Subring R, IsNoetherianRing S ∧
      (∀ i, (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆
        Set.range (MvPolynomial.map S.subtype)) ∧
      ∃ r₀ : ∀ i, MvPolynomial (Fin (n i)) S,
        (∀ i, MvPolynomial.map S.subtype (r₀ i) = r i) ∧
        ∃ d : ∀ i, Localization.Away (r₀ i) →+* Localization.Away (r i),
          (∀ i, (d i).comp
            (algebraMap (MvPolynomial (Fin (n i)) S) (Localization.Away (r₀ i))) =
            (algebraMap (MvPolynomial (Fin (n i)) R) (Localization.Away (r i))).comp
              (MvPolynomial.map S.subtype)) ∧
          (∀ i, Function.Injective (d i)) ∧ (∀ i k, x i k ∈ Set.range (d i)) ∧
          ∃ f₀ : ∀ i j, E i j →
            MvPolynomial (Fin (n i)) S →ₐ[S] Localization.Away (r₀ j),
            ∀ i j e, (f i j e).toRingHom.comp (MvPolynomial.map S.subtype) =
              (d j).comp (f₀ i j e).toRingHom := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i j) := Fintype.ofFinite (E i j)
  let _ (i) := Fintype.ofFinite (K i)
  let T (j) := (Σ i, E i j × Fin (n i)) ⊕ K j
  let _ (j) : Fintype (T j) :=
    inferInstanceAs (Fintype ((Σ i, E i j × Fin (n i)) ⊕ K j))
  let y : ∀ j, T j → Localization.Away (r j) := fun j t ↦ match t with
    | .inl ⟨i, e, k⟩ => f i j e (MvPolynomial.X k)
    | .inr k => x j k
  obtain ⟨S, hS, hs, r₀, hr, d, hd, hinj, hy⟩ :=
    exists_localized_coefficients n r y seed
  choose y₀ hy₀ using hy
  let f₀ (i j) (e : E i j) :
      MvPolynomial (Fin (n i)) S →ₐ[S] Localization.Away (r₀ j) :=
    MvPolynomial.aeval fun k ↦ y₀ j (.inl ⟨i, e, k⟩)
  refine ⟨S, hS, hs, r₀, hr, d, hd, hinj,
    fun i k ↦ ⟨y₀ i (.inr k), hy₀ i (.inr k)⟩, f₀, fun i j e ↦ ?_⟩
  apply MvPolynomial.ringHom_ext
  · intro a
    change f i j e (MvPolynomial.map S.subtype (MvPolynomial.C a)) =
      d j (f₀ i j e (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    change f i j e (algebraMap R (MvPolynomial (Fin (n i)) R) (S.subtype a)) = _
    rw [(f i j e).commutes]
    rw [IsScalarTower.algebraMap_apply S (MvPolynomial (Fin (n j)) S)]
    have h := RingHom.congr_fun (hd j) (MvPolynomial.C a)
    simp only [RingHom.comp_apply, MvPolynomial.map_C] at h
    exact h.symm
  · intro k
    change f i j e (MvPolynomial.map S.subtype (MvPolynomial.X k)) =
      d j (f₀ i j e (MvPolynomial.X k))
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact (hy₀ j (.inl ⟨i, e, k⟩)).symm

end FLT.Mazur.FinitePolynomialCoefficients
