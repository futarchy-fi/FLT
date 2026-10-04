/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor

/-! # A pointed Hopf fibre is the base change of the kernel

The chosen point is expressed by the A-algebra structure on S. Tensoring
the existing relative torsor isomorphism with that point gives the actual
coordinate-ring isomorphism, including its original coaction formula.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct
namespace HopfAlgebra
variable {R B A S : Type*} [CommRing R] [CommRing B] [CommRing A] [CommRing S]
  [HopfAlgebra R B] [HopfAlgebra R A] [Algebra B A] [IsScalarTower R B A]
  [Algebra R S] [Algebra B S] [Algebra A S]
  [IsScalarTower R A S] [IsScalarTower B A S]

/-- Translation by the chosen point identifies its fibre with the kernel. -/
def pointedFibreEquiv (f : B →ₐc[R] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A) :
    S ⊗[B] A ≃ₐ[S] S ⊗[R] (A ⧸ augmentationIdeal f) :=
  (cancelBaseChange B A S S A).symm |>.trans
    ((congr (AlgEquiv.refl : S ≃ₐ[S] S) (torsorEquiv f hf)).trans
      (cancelBaseChange R A S S (A ⧸ augmentationIdeal f)))

/-- The coordinate map is the original kernel coaction evaluated at the chosen point. -/
theorem pointedFibreEquiv_one_tmul (f : B →ₐc[R] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A) (a : A) :
    pointedFibreEquiv (S := S) f hf (1 ⊗ₜ[B] a) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A S)
        (AlgHom.id R (A ⧸ augmentationIdeal f)) (torsorCoaction f a) := by
  simp only [pointedFibreEquiv, AlgEquiv.trans_apply, cancelBaseChange_symm_tmul,
    congr_apply, map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply]
  have ht : torsorEquiv f hf (1 ⊗ₜ[B] a) = torsorCoaction f a := by
    change (1 ⊗ₜ[R] (1 : A ⧸ augmentationIdeal f)) * torsorCoaction f a = _
    exact one_mul _
  change cancelBaseChange R A S S _ (1 ⊗ₜ[A] torsorEquiv f hf (1 ⊗ₜ[B] a)) = _
  rw [ht]
  induction torsorCoaction f a using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Pure tensors retain their S-coordinate under the translation. -/
theorem pointedFibreEquiv_tmul (f : B →ₐc[R] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A) (s : S) (a : A) :
    pointedFibreEquiv f hf (s ⊗ₜ[B] a) =
      s • Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A S)
        (AlgHom.id R (A ⧸ augmentationIdeal f)) (torsorCoaction f a) := by
  have h : s • (1 ⊗ₜ[B] a) = s ⊗ₜ[B] a := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  calc
    _ = (pointedFibreEquiv f hf).toLinearEquiv (s • (1 ⊗ₜ[B] a)) :=
      congrArg (pointedFibreEquiv f hf) h.symm
    _ = s • pointedFibreEquiv f hf (1 ⊗ₜ[B] a) :=
      (pointedFibreEquiv f hf).toLinearEquiv.map_smul s _
    _ = _ := congrArg (s • ·) (pointedFibreEquiv_one_tmul f hf a)

end HopfAlgebra
