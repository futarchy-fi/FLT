/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierCotangentTensor

/-! # Naturality of the actual tensor representing an integral dual point -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A B S : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [HopfAlgebra R B]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]

/-- Evaluate an original-coordinate tensor against an original linear functional. -/
def coordinateTensorEquiv : A ⊗[R] S ≃ₗ[R] (Module.Dual R A →ₗ[R] S) :=
  TensorProduct.congr (Module.evalEquiv R A) (LinearEquiv.refl R S) ≪≫ₗ
    dualTensorHomEquiv R (Module.Dual R A) S

/-- The tensor comparison evaluates on pure tensors by the original pairing. -/
@[simp] theorem coordinateTensorEquiv_tmul (a : A) (s : S) (φ : Module.Dual R A) :
    coordinateTensorEquiv (a ⊗ₜ[R] s) φ = φ a • s := rfl

/-- The actual representing element evaluates as the given integral dual point. -/
@[simp] theorem coordinateTensorEquiv_dualElement
    (ψ : CartierDual R A →ₐ[R] S) (φ : Module.Dual R A) :
    coordinateTensorEquiv (testDualElement ψ) φ = ψ (WithConv.toConv φ) := by
  simp only [coordinateTensorEquiv, testDualElement, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rfl

/-- The representing element transports by the original coordinate map. -/
theorem testDualElement_naturality (f : A →ₐc[R] B) (ψ : CartierDual R A →ₐ[R] S) :
    f.toLinearMap.rTensor S (testDualElement ψ) = testDualElement (ψ.comp (map f)) := by
  apply (coordinateTensorEquiv (R := R) (A := B) (S := S)).injective
  ext φ
  have h (t : A ⊗[R] S) :
      coordinateTensorEquiv (f.toLinearMap.rTensor S t) φ =
        coordinateTensorEquiv t (φ.comp f.toLinearMap) := by
    induction t using TensorProduct.inductionOn with
    | tmul a s => rfl
    | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu]
  rw [h, coordinateTensorEquiv_dualElement, coordinateTensorEquiv_dualElement]
  rfl

/-- Original coefficients transport the representing element without choosing another basis. -/
theorem testDualElement_coefficients {T : Type} [CommRing T] [Algebra R T]
    (q : S →ₐ[R] T) (ψ : CartierDual R A →ₐ[R] S) :
    q.toLinearMap.lTensor A (testDualElement ψ) = testDualElement (q.comp ψ) := by
  rw [testDualElement_eq_sum (Module.Free.chooseBasis R A),
    testDualElement_eq_sum (Module.Free.chooseBasis R A)]
  simp

/-- The actual cotangent tensor respects coefficient reduction. -/
theorem testDlog_coefficients {T : Type} [CommRing T] [Algebra R T]
    (q : S →ₐ[R] T) (ψ : CartierDual R A →ₐ[R] S) :
    q.toLinearMap.lTensor _ (testDlog ψ) = testDlog (q.comp ψ) := by
  rw [testDlog_eq_sum (Module.Free.chooseBasis R A),
    testDlog_eq_sum (Module.Free.chooseBasis R A)]
  simp

end HopfAlgebra.CartierDual
