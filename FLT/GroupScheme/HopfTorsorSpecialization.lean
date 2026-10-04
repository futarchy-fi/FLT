/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor

/-!
# Specializing the canonical Hopf torsor comparison

The relative Hopf comparison can be pulled back along any algebra over the
middle coordinate ring. No comparison isomorphism is supplied as an input.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace HopfAlgebra

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R B]
  [Algebra B A] [IsScalarTower R B A]
  [Algebra R C] [Algebra B C] [Algebra A C]
  [IsScalarTower R B C] [IsScalarTower R A C] [IsScalarTower B A C]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)

/-- Base change of the canonical comparison, with tensor associators cancelled. -/
def specializedTorsorEquiv :
    C ⊗[B] A ≃ₐ[C] C ⊗[R] (A ⧸ augmentationIdeal f) :=
  (cancelBaseChange B A C C A).symm.trans
    ((congr (AlgEquiv.refl : C ≃ₐ[C] C) (torsorEquiv f hf)).trans
      (cancelBaseChange R A C C (A ⧸ augmentationIdeal f)))

omit [IsScalarTower R B C] in
/-- The second coordinate remains the actual Hopf coaction after specialization. -/
theorem specializedTorsorEquiv_second (a : A) :
    specializedTorsorEquiv (C := C) f hf (1 ⊗ₜ[B] a) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A C)
        (AlgHom.id R (A ⧸ augmentationIdeal f)) (torsorCoaction f a) := by
  change cancelBaseChange R A C C (A ⧸ augmentationIdeal f)
    (1 ⊗ₜ[A] (torsorEquiv f hf (1 ⊗ₜ[B] a))) = _
  have he : torsorEquiv f hf (1 ⊗ₜ[B] a) = torsorCoaction f a := by
    simp [torsorEquiv, torsorHom, torsorCoactionOverBase, ← Algebra.TensorProduct.one_def]
  rw [he]
  generalize torsorCoaction f a = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end HopfAlgebra
