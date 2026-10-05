/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialRelationIntegerModel

/-!
# Integer models preserving finitely many sections and equations

A finite list of elements of a finitely presented algebra, together with
finitely many integer polynomial equations among them, descends to an
integer model. Inverse equations and cocycle equations are special cases.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v w

/-- Descend marked elements and their finite system of polynomial equations.
The recovered algebra is identified by tensor product, not by an assumed
injection of the model into the original algebra. -/
theorem exists_integer_model_marked {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B]
    {κ : Type v} [Finite κ] {τ : Type w} [Finite τ]
    (x : κ → B) (r : τ → MvPolynomial κ ℤ) (hr : ∀ l, aeval x (r l) = 0)
    (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        Algebra.FinitePresentation A₀ B₀ ∧
          ∃ (e : A ⊗[A₀] B₀ ≃ₐ[A] B) (x₀ : κ → B₀),
            (∀ k, e (1 ⊗ₜ x₀ k) = x k) ∧ ∀ l, aeval x₀ (r l) = 0 := by
  let P := Algebra.Presentation.ofFinitePresentation A B
  let u := fun k ↦ P.σ (x k)
  let q := fun l ↦ aeval u (r l)
  have hq (l) : aeval P.val (q l) = 0 := by
    change ((aeval P.val).restrictScalars ℤ) (aeval u (r l)) = 0
    rw [comp_aeval_apply]
    simpa only [u, AlgHom.restrictScalars_apply, P.aeval_val_σ] using hr l
  let t : Set A := s ∪ ⋃ k, (u k).coeffs
  have ht : t.Finite := hs.union (Set.finite_iUnion fun k ↦ (u k).coeffs.finite_toSet)
  obtain ⟨A₀, hA₀, ht₀, hP, q₀, hq₀, hzero⟩ :=
    exists_integer_model_relations P q hq t ht
  let := hP
  have hu (k) : u k ∈ Set.range (map (algebraMap A₀ A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, ht₀ (Or.inr (Set.mem_iUnion.mpr ⟨k, ha⟩))⟩, rfl⟩
  choose u₀ hu₀ using hu
  let B₀ := P.ModelOfHasCoeffs A₀
  let π : MvPolynomial _ A₀ →+* B₀ := Ideal.Quotient.mk _
  let x₀ := fun k ↦ π (u₀ k)
  refine ⟨A₀, hA₀, fun a ha ↦ ht₀ (Or.inl ha), B₀, inferInstance, inferInstance,
    inferInstance, P.tensorModelOfHasCoeffsEquiv A₀, x₀, ?_, ?_⟩
  · intro k
    change P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ Ideal.Quotient.mk _ (u₀ k)) = x k
    rw [P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
      ← MvPolynomial.aeval_map_algebraMap A, hu₀]
    exact P.aeval_val_σ (x k)
  · intro l
    have heq : aeval u₀ (r l) = q₀ l := by
      apply MvPolynomial.map_injective (f := algebraMap A₀ A) Subtype.val_injective
      change (map (algebraMap A₀ A)).toIntAlgHom (aeval u₀ (r l)) = _
      rw [comp_aeval_apply (R := ℤ) (f := u₀)]
      simpa only [RingHom.toIntAlgHom_apply, hu₀] using (hq₀ l).symm
    change aeval (fun k ↦ π.toIntAlgHom (u₀ k)) (r l) = 0
    rw [← comp_aeval_apply (R := ℤ) (f := u₀) π.toIntAlgHom, heq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hzero l)

end FLT.Mazur.Approximation
