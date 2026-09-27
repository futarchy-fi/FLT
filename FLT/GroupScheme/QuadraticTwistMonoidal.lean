/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistTensor

/-!
# Tensor compatibility of quadratic fixed algebras

The tensor comparison for scalar extension intertwines the quadratic descent
actions. Restricting it to fixed algebras gives the target needed to descend
comultiplication.
-/

@[expose] public section

open scoped TensorProduct

namespace QuadraticDescent

universe v
variable {R B C : Type v} [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C]

/-- An equivariant algebra equivalence restricts to an equivalence of fixed algebras. -/
noncomputable def fixedEquiv (σ : B ≃ₐ[R] B) (τ : C ≃ₐ[R] C) (e : B ≃ₐ[R] C)
    (he : ∀ x, τ (e x) = e (σ x)) : fixed σ ≃ₐ[R] fixed τ := by
  refine AlgEquiv.ofBijective (fixedMap σ τ e.toAlgHom he) ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  · intro y
    have hy : σ (e.symm y.val) = e.symm y.val := by
      apply e.injective
      rw [← he, e.apply_symm_apply]
      exact y.property
    exact ⟨⟨e.symm y.val, hy⟩, Subtype.ext (e.apply_symm_apply y.val)⟩

end QuadraticDescent

namespace QuadraticTwist

universe v

/-- Tensoring two scalar extensions over their coefficients is scalar extension of the tensor. -/
noncomputable def tensorBaseChange (R S A B : Type v) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B] :
    (S ⊗[R] A) ⊗[S] (S ⊗[R] B) ≃ₐ[S] S ⊗[R] (A ⊗[R] B) :=
  (Algebra.TensorProduct.cancelBaseChange R S S (S ⊗[R] A) B).trans
    (Algebra.TensorProduct.assoc R R S S A B)

/-- The tensor comparison multiplies the two coefficients. -/
@[simp] theorem tensorBaseChange_tmul (R S A B : Type v) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B]
    (s t : S) (a : A) (b : B) :
    tensorBaseChange R S A B ((s ⊗ₜ[R] a) ⊗ₜ[S] (t ⊗ₜ[R] b)) =
      (t * s) ⊗ₜ[R] (a ⊗ₜ[R] b) := rfl

/-- The inverse tensor comparison inserts a unit in the second coefficient. -/
@[simp] theorem tensorBaseChange_symm_tmul (R S A B : Type v) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B]
    (s : S) (a : A) (b : B) :
    (tensorBaseChange R S A B).symm (s ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      (s ⊗ₜ[R] a) ⊗ₜ[S] (1 ⊗ₜ[R] b) := rfl

variable {R H J : Type v} [CommRing R] [CommRing H] [CommRing J]
variable [Algebra R H] [Algebra R J]
variable (d : R) (ι : H ≃ₐ[R] H) (κ : J ≃ₐ[R] J)

/-- Combining tensors respects the two semilinear descent actions. -/
theorem tensorBaseChange_equivariant (x : QuadraticAlgebra R d 0 ⊗[R] H)
    (y : QuadraticAlgebra R d 0 ⊗[R] J) :
    involution d (Algebra.TensorProduct.congr ι κ)
        (tensorBaseChange R (QuadraticAlgebra R d 0) H J (x ⊗ₜ y)) =
      tensorBaseChange R (QuadraticAlgebra R d 0) H J
        (involution d ι x ⊗ₜ involution d κ y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy']
    | tmul t b =>
      change conjugation d (t * s) ⊗ₜ[R] (ι a ⊗ₜ[R] κ b) =
        (conjugation d t * conjugation d s) ⊗ₜ[R] (ι a ⊗ₜ[R] κ b)
      rw [map_mul]

variable (u : Rˣ) (hι : Function.Involutive ι) (hκ : Function.Involutive κ)
variable (r : R) (hr : 2 * r = 1)

/-- Scalar recovery on both factors induces scalar recovery of their tensor product. -/
noncomputable def tensorScalarExtensionEquiv :
    QuadraticAlgebra R (u : R) 0 ⊗[R] (model (u : R) ι ⊗[R] model (u : R) κ)
      ≃ₐ[QuadraticAlgebra R (u : R) 0] QuadraticAlgebra R (u : R) 0 ⊗[R] (H ⊗[R] J) :=
  (tensorBaseChange R (QuadraticAlgebra R (u : R) 0)
      (model (u : R) ι) (model (u : R) κ)).symm.trans
    ((Algebra.TensorProduct.congr (scalarExtensionEquivOver u ι hι r hr)
      (scalarExtensionEquivOver u κ hκ r hr)).trans
        (tensorBaseChange R (QuadraticAlgebra R (u : R) 0) H J))

/-- Scalar recovery on a tensor of two fixed elements. -/
theorem tensorScalarExtensionEquiv_tmul (s : QuadraticAlgebra R (u : R) 0)
    (a : model (u : R) ι) (b : model (u : R) κ) :
    tensorScalarExtensionEquiv ι κ u hι hκ r hr (s ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      tensorBaseChange R (QuadraticAlgebra R (u : R) 0) H J
        (((s ⊗ₜ[R] (1 : H)) * a.val) ⊗ₜ b.val) := by
  change tensorBaseChange R (QuadraticAlgebra R (u : R) 0) H J
    (scalarExtensionEquiv u ι hι r hr (s ⊗ₜ[R] a) ⊗ₜ
      scalarExtensionEquiv u κ hκ r hr (1 ⊗ₜ[R] b)) = _
  simp only [scalarExtensionEquiv_tmul, ← Algebra.TensorProduct.one_def, one_mul]

/-- The tensor scalar-recovery equivalence intertwines coefficient conjugation and descent. -/
theorem tensorScalarExtensionEquiv_equivariant
    (z : QuadraticAlgebra R (u : R) 0 ⊗[R] (model (u : R) ι ⊗[R] model (u : R) κ)) :
    involution (u : R) (Algebra.TensorProduct.congr ι κ)
        (tensorScalarExtensionEquiv ι κ u hι hκ r hr z) =
      tensorScalarExtensionEquiv ι κ u hι hκ r hr
        (involution (u : R) AlgEquiv.refl z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
    | tmul a b =>
      change involution (u : R) (Algebra.TensorProduct.congr ι κ)
        (tensorScalarExtensionEquiv ι κ u hι hκ r hr (s ⊗ₜ[R] (a ⊗ₜ[R] b))) =
          tensorScalarExtensionEquiv ι κ u hι hκ r hr
            (conjugation (u : R) s ⊗ₜ[R] (a ⊗ₜ[R] b))
      rw [tensorScalarExtensionEquiv_tmul, tensorBaseChange_equivariant,
        tensorScalarExtensionEquiv_tmul, map_mul]
      have ha : involution (u : R) ι a.val = a.val := a.property
      have hb : involution (u : R) κ b.val = b.val := b.property
      rw [ha, hb]
      simp [involution]

/-- Tensor products commute with taking the quadratic fixed models. -/
noncomputable def modelTensorEquiv :
    model (u : R) ι ⊗[R] model (u : R) κ ≃ₐ[R]
      model (u : R) (Algebra.TensorProduct.congr ι κ) :=
  (trivialModelEquiv r hr (u : R)).symm.trans
    (QuadraticDescent.fixedEquiv (involution (u : R) AlgEquiv.refl)
      (involution (u : R) (Algebra.TensorProduct.congr ι κ))
      ((tensorScalarExtensionEquiv ι κ u hι hκ r hr).restrictScalars R)
      (tensorScalarExtensionEquiv_equivariant ι κ u hι hκ r hr))

/-- The fixed tensor comparison is scalar recovery at coefficient one. -/
theorem modelTensorEquiv_apply (z : model (u : R) ι ⊗[R] model (u : R) κ) :
    (modelTensorEquiv ι κ u hι hκ r hr z :
        QuadraticAlgebra R (u : R) 0 ⊗[R] (H ⊗[R] J)) =
      tensorScalarExtensionEquiv ι κ u hι hκ r hr (1 ⊗ₜ[R] z) := rfl

/-- On fixed pure tensors the comparison is the ordinary balanced tensor comparison. -/
@[simp] theorem modelTensorEquiv_tmul (a : model (u : R) ι) (b : model (u : R) κ) :
    (modelTensorEquiv ι κ u hι hκ r hr (a ⊗ₜ[R] b) :
        QuadraticAlgebra R (u : R) 0 ⊗[R] (H ⊗[R] J)) =
      tensorBaseChange R (QuadraticAlgebra R (u : R) 0) H J (a.val ⊗ₜ b.val) := by
  rw [modelTensorEquiv_apply, tensorScalarExtensionEquiv_tmul]
  simp only [← Algebra.TensorProduct.one_def, one_mul]

end QuadraticTwist
