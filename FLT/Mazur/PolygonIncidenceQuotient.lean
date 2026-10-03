/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonIncidence
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Kernel and cokernel of cyclic incidence

Evaluation at the initial vertex identifies the kernel with the coefficient
field; summation identifies the cokernel with that field. Neither construction
divides by the number of vertices. These are linear algebra calculations, not
an identification with the structure-sheaf cohomology of a polygon.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonIncidence

variable (K : Type*) [Field K] {n : ℕ} (hn : 0 < n)

/-- The kernel of cyclic difference is the line of constant functions. -/
def kernelEquiv : LinearMap.ker (difference K hn) ≃ₗ[K] K where
  toFun v := v.val ⟨0, hn⟩
  invFun a := ⟨constant K n a, by ext i; simp⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    exact (eq_initial_of_difference_eq_zero hn v.val v.property i).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem kernelEquiv_apply (v : LinearMap.ker (difference K hn)) :
    kernelEquiv K hn v = v.val ⟨0, hn⟩ := rfl

/-- The inverse sends a scalar to the constant vector. -/
theorem kernelEquiv_symm_apply (a : K) :
    ((kernelEquiv K hn).symm a).val = constant K n a := rfl

/-- Summation identifies the incidence cokernel with the field. -/
def cokernelEquiv :
    ((Fin n → K) ⧸ LinearMap.range (difference K hn)) ≃ₗ[K] K :=
  (Submodule.quotEquivOfEq _ _ (range_difference K hn)).trans
    ((total K n).quotKerEquivOfSurjective (total_surjective K hn))

@[simp]
theorem cokernelEquiv_mk (v : Fin n → K) :
    cokernelEquiv K hn (Submodule.Quotient.mk v) = total K n v := by
  rfl

/-- The incidence kernel has dimension one, also for a one-vertex cycle. -/
theorem finrank_kernel : Module.finrank K (LinearMap.ker (difference K hn)) = 1 := by
  rw [(kernelEquiv K hn).finrank_eq]
  exact Module.finrank_self K

/-- The incidence cokernel has dimension one in every characteristic. -/
theorem finrank_cokernel :
    Module.finrank K ((Fin n → K) ⧸ LinearMap.range (difference K hn)) = 1 := by
  rw [(cokernelEquiv K hn).finrank_eq]
  exact Module.finrank_self K

/-- Equality of incidence classes is exactly equality of total values. -/
theorem mk_eq_mk_iff_total_eq (v w : Fin n → K) :
    (Submodule.Quotient.mk v : (Fin n → K) ⧸ LinearMap.range (difference K hn)) =
      Submodule.Quotient.mk w ↔ total K n v = total K n w :=
  (cokernelEquiv K hn).injective.eq_iff.symm

end FLT.Mazur.PolygonIncidence
