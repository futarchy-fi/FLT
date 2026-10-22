/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealInclusionFlatExtension
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Residual flatness under flat target extension

A flat extension of the target preserves flatness of the residual algebra.
Tensor cancellation gives the comparison over the original ring; quotient
surjectivity upgrades it to the required quotient-linear equivalence.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ResidualFlatTargetExtension
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (T : Type*) [CommRing T] [Algebra R T] [Algebra A T] [IsScalarTower R A T]

/-- Residual flatness persists under a flat extension of the target algebra. -/
theorem flat [Module.Flat A T] (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)] :
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] T) := by
  let _ : Algebra (R ⧸ I) (A ⊗[R] (R ⧸ I)) := Algebra.TensorProduct.rightAlgebra
  let _ : Module.Flat (R ⧸ I) (A ⊗[R] (R ⧸ I)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight R (R ⧸ I) A).symm.toLinearEquiv
  let _ : Module.Flat (R ⧸ I) ((A ⊗[R] (R ⧸ I)) ⊗[A] T) :=
    Module.Flat.trans (R ⧸ I) (A ⊗[R] (R ⧸ I)) _
  let e : ((A ⊗[R] (R ⧸ I)) ⊗[A] T) ≃ₗ[R] (R ⧸ I) ⊗[R] T :=
    ((TensorProduct.comm A (A ⊗[R] (R ⧸ I)) T).restrictScalars R).trans
      (((AlgebraTensorModule.cancelBaseChange R A A T (R ⧸ I)).restrictScalars R).trans
        (TensorProduct.comm R T (R ⧸ I)))
  let e' : ((A ⊗[R] (R ⧸ I)) ⊗[A] T) ≃ₗ[R ⧸ I] (R ⧸ I) ⊗[R] T :=
    { e.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        change e ((algebraMap R (R ⧸ I) r) • x) = (algebraMap R (R ⧸ I) r) • e x
        have hs : (algebraMap R (R ⧸ I) r) • x = r • x := by
          induction x with
          | tmul d t => rw [smul_tmul', smul_tmul', algebraMap_smul]
          | add x y hx hy =>
            rw [TensorProduct.smul_add, hx, hy, TensorProduct.smul_add]
        rw [hs, algebraMap_smul]
        exact e.map_smul r x }
  exact Module.Flat.of_linearEquiv e'.symm

/-- In particular localizing the target preserves flatness of its residual algebra. -/
theorem localization_flat (U : Submonoid A) [IsLocalization U T] (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)] :
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] T) := by
  let _ := IsLocalization.flat T U
  exact flat (A := A) T I

end FLT.Mazur.ResidualFlatTargetExtension
