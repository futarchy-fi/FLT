/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIteratedPolynomialCoefficients
public import FLT.Mazur.PolynomialCoefficientArrow

/-!
# Coefficient squares for diagrams with iterated principal targets

Polynomial arrows into both levels descend together, including all additional
fraction data. Every second target retains its prescribed denominator.
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

/-- Descend both levels of a finite diagram through one coefficient ring. -/
theorem exists_iterated_diagram_coefficients
    (f : ∀ i j, E i j → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j))
    (g : ∀ i j k, H i j k →
      MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (s j k))
    (x : ∀ i, K i → Localization.Away (r i))
    (y : ∀ i j, L i j → Localization.Away (s i j))
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
          ∃ s₀ : ∀ i, J i → Localization.Away (r₀ i),
            (∀ i j, d i (s₀ i j) = s i j) ∧
            ∃ e : ∀ i j, Localization.Away (s₀ i j) →+* Localization.Away (s i j),
              (∀ i j, (e i j).comp
                (algebraMap (Localization.Away (r₀ i)) (Localization.Away (s₀ i j))) =
                (algebraMap (Localization.Away (r i)) (Localization.Away (s i j))).comp
                  (d i)) ∧
              (∀ i j, Function.Injective (e i j)) ∧
              (∀ i j k, y i j k ∈ Set.range (e i j)) ∧
              (∃ f₀ : ∀ i j, E i j →
                MvPolynomial (Fin (n i)) S →ₐ[S] Localization.Away (r₀ j),
                ∀ i j a, (f i j a).toRingHom.comp (MvPolynomial.map S.subtype) =
                  (d j).comp (f₀ i j a).toRingHom) ∧
              ∃ g₀ : ∀ i j k, H i j k →
                MvPolynomial (Fin (n i)) S →ₐ[S] Localization.Away (s₀ j k),
                ∀ i j k a, (g i j k a).toRingHom.comp (MvPolynomial.map S.subtype) =
                  (e j k).comp (g₀ i j k a).toRingHom := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i) := Fintype.ofFinite (K i)
  let _ (i j) := Fintype.ofFinite (L i j)
  let _ (i j) := Fintype.ofFinite (E i j)
  let _ (i j k) := Fintype.ofFinite (H i j k)
  let T (j) := (Σ i, E i j × Fin (n i)) ⊕ K j
  let U (j) (k : J j) := (Σ i, H i j k × Fin (n i)) ⊕ L j k
  let _ (j) : Fintype (T j) :=
    inferInstanceAs (Fintype ((Σ i, E i j × Fin (n i)) ⊕ K j))
  let _ (j k) : Fintype (U j k) :=
    inferInstanceAs (Fintype ((Σ i, H i j k × Fin (n i)) ⊕ L j k))
  let x' : ∀ j, T j → Localization.Away (r j) := fun j a ↦ match a with
    | .inl ⟨i, a, k⟩ => f i j a (MvPolynomial.X k)
    | .inr k => x j k
  let y' : ∀ j k, U j k → Localization.Away (s j k) := fun j k a ↦ match a with
    | .inl ⟨i, a, l⟩ => g i j k a (MvPolynomial.X l)
    | .inr l => y j k l
  obtain ⟨S, hS, hseed, r₀, hr, d, hd, hinj, hx, s₀, hs, e, he, heinj, hy⟩ :=
    exists_iterated_coefficients n r s x' y' seed
  have hdS (j) : (d j).comp (algebraMap S (Localization.Away (r₀ j))) =
      (algebraMap R (Localization.Away (r j))).comp S.subtype := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply S (MvPolynomial (Fin (n j)) S),
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin (n j)) R)]
    have h := RingHom.congr_fun (hd j) (MvPolynomial.C a)
    simpa only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.algebraMap_eq] using h
  have heS (j k) : (e j k).comp (algebraMap S (Localization.Away (s₀ j k))) =
      (algebraMap R (Localization.Away (s j k))).comp S.subtype := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply S (Localization.Away (r₀ j))]
    have h := RingHom.congr_fun (he j k)
      (algebraMap S (Localization.Away (r₀ j)) a)
    simp only [RingHom.comp_apply] at h
    rw [h]
    have h' := RingHom.congr_fun (hdS j) a
    simp only [RingHom.comp_apply] at h'
    rw [h']
    exact (IsScalarTower.algebraMap_apply R (Localization.Away (r j)) _ _).symm
  choose f₀ hf₀ using fun i j a ↦ exists_polynomial_coefficient_arrow S (d j)
    (hdS j) (f i j a) (fun k ↦ hx j (.inl ⟨i, a, k⟩))
  choose g₀ hg₀ using fun i j k a ↦ exists_polynomial_coefficient_arrow S (e j k)
    (heS j k) (g i j k a) (fun l ↦ hy j k (.inl ⟨i, a, l⟩))
  exact ⟨S, hS, hseed, r₀, hr, d, hd, hinj, fun i k ↦ hx i (.inr k), s₀, hs,
    e, he, heinj, fun i j k ↦ hy i j (.inr k), ⟨f₀, hf₀⟩, g₀, hg₀⟩

end FLT.Mazur.FinitePolynomialCoefficients
