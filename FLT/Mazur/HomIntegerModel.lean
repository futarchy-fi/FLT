/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MarkedIntegerModel

/-!
# Descending maps from a finite-type integer algebra

A map from a fixed finite-type integer algebra to a finitely presented
algebra descends together with a coefficient model of the target. This
constructs the map from images of generators and descended relations.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Maps from a fixed finite-type integer algebra descend to a finite stage,
with the whole target algebra recovered by base change. -/
theorem exists_integer_model_hom {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra.FinitePresentation A B] [Algebra.FiniteType ℤ C]
    (φ : C →+* B) (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        Algebra.FinitePresentation A₀ B₀ ∧
          ∃ (e : A ⊗[A₀] B₀ ≃ₐ[A] B) (φ₀ : C →+* B₀),
            ∀ c, e (1 ⊗ₜ φ₀ c) = φ c := by
  let : Algebra.FinitePresentation ℤ C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let Q := Algebra.Presentation.ofFinitePresentation ℤ C
  let x := fun i ↦ φ (Q.val i)
  have hr (j) : aeval x (Q.relation j) = 0 := by
    change aeval (fun i ↦ φ.toIntAlgHom (Q.val i)) (Q.relation j) = 0
    rw [← comp_aeval_apply, Q.aeval_val_relation, map_zero]
  obtain ⟨A₀, hA₀, hs₀, B₀, _, _, hB₀, e, x₀, hx₀, hr₀⟩ :=
    exists_integer_model_marked (A := A) x Q.relation hr s hs
  have hker : Q.ker ≤ RingHom.ker (aeval x₀) := by
    rw [← Q.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hr₀ j
  let φ₀ : C →ₐ[ℤ] B₀ := (Ideal.Quotient.liftₐ Q.ker (aeval x₀) hker).comp
    (Q.quotientEquiv.restrictScalars ℤ).symm.toAlgHom
  have hlift (p : Q.Ring) : φ₀ (aeval Q.val p) = aeval x₀ p := by
    rw [← Q.algebraMap_apply, ← Q.quotientEquiv_mk]
    change (Ideal.Quotient.liftₐ Q.ker (aeval x₀) hker)
      ((Q.quotientEquiv.restrictScalars ℤ).symm
        ((Q.quotientEquiv.restrictScalars ℤ) (Ideal.Quotient.mk _ p))) = _
    rw [AlgEquiv.symm_apply_apply]
    rfl
  let g : B₀ →ₐ[ℤ] B := (e.toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom).toIntAlgHom
  have hg (i) : g (x₀ i) = φ (Q.val i) := hx₀ i
  refine ⟨A₀, hA₀, hs₀, B₀, inferInstance, inferInstance, hB₀, e, φ₀.toRingHom, ?_⟩
  intro c
  change g (φ₀ c) = φ.toIntAlgHom c
  rw [← Q.aeval_val_σ c, hlift, comp_aeval_apply, comp_aeval_apply]
  simp only [hg, RingHom.toIntAlgHom_apply]

end FLT.Mazur.Approximation
