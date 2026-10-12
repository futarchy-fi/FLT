/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianBlockTransition
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Scalar extension of finite ambient decompositions

Finite split coordinates commute with scalar extension. Conjugating the tensor
extension of an ambient equivalence gives an actual equivalence over every algebra.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (ι : Type*) [Fintype ι] (d : ℕ)

/-- Finite split coordinates on the scalar extension of the ambient module. -/
def splitAmbientTensorEquiv :
    S ⊗[R] ((Fin d → R) × (ι → R)) ≃ₗ[S] ((Fin d → S) × (ι → S)) := by
  classical
  exact (TensorProduct.prodRight R S S _ _).trans
    ((TensorProduct.piScalarRight R S S (Fin d)).prodCongr
      (TensorProduct.piScalarRight R S S ι))

/-- Pure tensors have their expected coordinatewise scalar extension. -/
theorem splitAmbientTensorEquiv_tmul (s : S) (x : (Fin d → R) × (ι → R)) :
    splitAmbientTensorEquiv S ι d (s ⊗ₜ[R] x) =
      ((fun i ↦ algebraMap R S (x.1 i) * s), fun j ↦ algebraMap R S (x.2 j) * s) := by
  simp [splitAmbientTensorEquiv, Algebra.smul_def]

variable {ι} {κ : Type*} [Fintype κ] {d}

/-- The scalar-extended ambient coordinate equivalence, constructed by tensor extension. -/
def ambientEquivBaseChange
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R))) :
    ((Fin d → S) × (κ → S)) ≃ₗ[S] ((Fin d → S) × (ι → S)) :=
  (splitAmbientTensorEquiv S κ d).symm.trans
    ((e.baseChange R S).trans (splitAmbientTensorEquiv S ι d))

/-- The constructed equivalence agrees with the original one on scalar-extended vectors. -/
theorem ambientEquivBaseChange_algebraMap
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
    (x : (Fin d → R) × (κ → R)) :
    ambientEquivBaseChange S e
      ((fun i ↦ algebraMap R S (x.1 i)), fun j ↦ algebraMap R S (x.2 j)) =
        ((fun i ↦ algebraMap R S ((e x).1 i)), fun j ↦ algebraMap R S ((e x).2 j)) := by
  have hx := splitAmbientTensorEquiv_tmul S κ d 1 x
  simp only [mul_one] at hx
  rw [← hx]
  simp only [ambientEquivBaseChange, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]
  simpa only [mul_one] using splitAmbientTensorEquiv_tmul S ι d 1 (e x)

/-- Scalar extension preserves the inverse ambient coordinate change. -/
theorem ambientEquivBaseChange_symm
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R))) :
    ambientEquivBaseChange S e.symm = (ambientEquivBaseChange S e).symm := by
  simp only [ambientEquivBaseChange, LinearEquiv.baseChange_symm,
    LinearEquiv.trans_symm, LinearEquiv.symm_symm]
  rfl

end FLT.Mazur.GrassmannianChart
