/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.GaloisTensorPrime
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Unramified.Field

/-!
# The coefficient overlap is reduced and Galois evaluations detect its elements

Finite subalgebras are separable fields. Their tensor extensions are reduced,
and flat passage to the union proves reducedness of the original infinite
extension. The prime classification then makes Galois evaluation faithful.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.GaloisTensorPrime

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [CharZero K] [Algebra.IsAlgebraic K L]

/-- The actual tensor overlap of an algebraic characteristic-zero field extension is reduced. -/
instance tensor_isReduced : IsReduced (L ⊗[K] L) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  let _ : Field B := B.isField_of_algebraic.toField
  let _ : Algebra.FiniteType K B := B.fg_iff_finiteType.mp hB
  let _ : Algebra.IsAlgebraic K B := Algebra.IsAlgebraic.of_injective B.val Subtype.val_injective
  let _ : Algebra.FormallyUnramified K B := Algebra.FormallyUnramified.of_isSeparable K B
  exact Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[K] B)

variable [IsAlgClosed L]

/-- Equality of original tensor coefficients is detected by all Galois evaluations. -/
theorem evaluation_ext (x y : L ⊗[K] L)
    (h : ∀ g : L ≃ₐ[K] L, evaluation g x = evaluation g y) : x = y := by
  apply sub_eq_zero.mp
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let _ := hP
  obtain ⟨g, hg⟩ := exists_evaluation_ker P
  rw [← hg]
  change evaluation g (x - y) = 0
  rw [map_sub, h g, sub_self]

end FLT.Mazur.GaloisTensorPrime
