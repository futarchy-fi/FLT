/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonRelationIntegerModel

/-!
# Simultaneous descent of finitely many affine algebra maps

Choose polynomial representatives for images of generators. Descend their
coefficients and the witnesses that source relations vanish in the target.
Additional finite equations may be retained for subsequent diagram laws.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial

namespace FLT.Mazur.Approximation

universe u v w

/-- Coefficient change commutes with substitution of polynomials. -/
theorem map_aeval_polynomial {R S : Type*} [CommRing R] [CommRing S]
    {σ τ : Type*} (f : R →+* S) (x : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) :
    map f (aeval x p) = aeval (fun i ↦ map f (x i)) (map f p) :=
  map_eval₂ f x p

/-- All arrows of a finite affine family descend over one coefficient stage,
while retaining a prescribed finite family of vanishing equations. -/
theorem exists_integer_model_arrows {A : Type u} [CommRing A]
    {ι E : Type v} [Finite ι] [Finite E] (B : ι → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : ι → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (src dst : E → ι) (φ : ∀ e, B (src e) →ₐ[A] B (dst e))
    (κ : ι → Type w) [∀ i, Finite (κ i)]
    (q : ∀ i, κ i → MvPolynomial (Fin (n i)) A)
    (hq : ∀ i k, aeval (P i).val (q i k) = 0) (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ _hP : ∀ i, (P i).HasCoeffs A₀,
        ∃ x₀ : ∀ e, Fin (n (src e)) → MvPolynomial (Fin (n (dst e))) A₀,
          (∀ e a, map (algebraMap A₀ A) (x₀ e a) =
            (P (dst e)).σ (φ e ((P (src e)).val a))) ∧
          (∃ φ₀ : ∀ e, (P (src e)).ModelOfHasCoeffs A₀ →ₐ[A₀]
              (P (dst e)).ModelOfHasCoeffs A₀,
            ∀ e p, φ₀ e (Ideal.Quotient.mk _ p) =
              Ideal.Quotient.mk _ (aeval (x₀ e) p)) ∧
          ∀ i k (q₀ : MvPolynomial (Fin (n i)) A₀),
            map (algebraMap A₀ A) q₀ = q i k →
              (Ideal.Quotient.mk _ q₀ : (P i).ModelOfHasCoeffs A₀) = 0 := by
  classical
  let x := fun e a ↦ (P (dst e)).σ (φ e ((P (src e)).val a))
  have hx (e) (a) : aeval (P (dst e)).val (x e a) =
      φ e ((P (src e)).val a) := (P (dst e)).aeval_val_σ _
  let K := fun i ↦ κ i ⊕ (Σ e : {e : E // dst e = i}, Fin (m (src e.val)))
  let r : ∀ i, K i → MvPolynomial (Fin (n i)) A := fun i ↦ Sum.elim (q i)
    (fun ⟨⟨e, h⟩, b⟩ ↦ h ▸ aeval (x e) ((P (src e)).relation b))
  have hr (i) (k : K i) : aeval (P i).val (r i k) = 0 := by
    rcases k with k | ⟨⟨e, h⟩, b⟩
    · exact hq i k
    · subst i
      change aeval (P (dst e)).val (aeval (x e) ((P (src e)).relation b)) = 0
      rw [comp_aeval_apply]
      simp only [hx, ← comp_aeval_apply, (P (src e)).aeval_val_relation, map_zero]
  let t : Set A := s ∪ ⋃ e, ⋃ a, (x e a).coeffs
  have ht : t.Finite := hs.union (Set.finite_iUnion fun e ↦
    Set.finite_iUnion fun a ↦ (x e a).coeffs.finite_toSet)
  obtain ⟨A₀, hA₀, ht₀, hP, hz⟩ :=
    exists_common_integer_relation_models B n m P K r hr t ht
  let := hP
  have hl (e) (a) : x e a ∈ Set.range (map (algebraMap A₀ A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    exact ⟨⟨c, ht₀ (Or.inr (Set.mem_iUnion.mpr ⟨e,
      Set.mem_iUnion.mpr ⟨a, hc⟩⟩))⟩, rfl⟩
  choose x₀ hx₀ using hl
  let π := fun i ↦ Ideal.Quotient.mkₐ A₀
    (Ideal.span (Set.range ((P i).relationOfHasCoeffs A₀)))
  have hrel (e) (b) : (π (dst e)).comp (aeval (x₀ e))
      ((P (src e)).relationOfHasCoeffs A₀ b) = 0 := by
    apply hz (dst e) (.inr ⟨⟨e, rfl⟩, b⟩)
    change map (algebraMap A₀ A)
      (aeval (x₀ e) ((P (src e)).relationOfHasCoeffs A₀ b)) =
        aeval (x e) ((P (src e)).relation b)
    rw [map_aeval_polynomial, (P (src e)).map_relationOfHasCoeffs]
    simp only [hx₀]
  let φ₀ := fun e ↦ Ideal.Quotient.liftₐ
    (Ideal.span (Set.range ((P (src e)).relationOfHasCoeffs A₀))) ((π (dst e)).comp (aeval (x₀ e)))
    (by
      change Ideal.span _ ≤ RingHom.ker _
      rw [Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      exact hrel e b)
  exact ⟨A₀, hA₀, fun a ha ↦ ht₀ (Or.inl ha), hP, x₀, hx₀,
    ⟨φ₀, fun _ _ ↦ rfl⟩, fun i k q₀ hq₀ ↦ hz i (.inl k) q₀ hq₀⟩

end FLT.Mazur.Approximation
