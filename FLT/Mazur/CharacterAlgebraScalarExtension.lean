/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Explicit scalar extension of arithmetic character algebras

The additive monoid algebra commutes with scalar extension. Sealed coordinates
retain both tensor factors and every character without unfolding the tensor model.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.CharacterAlgebraScalarExtension

variable (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid M]

/-- Change only the coefficients of the character algebra. -/
def coeff : AddMonoidAlgebra R M →ₐ[R] AddMonoidAlgebra A M :=
  AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R A)

/-- The actual scalar tensor equivalence, with a sealed implementation. -/
irreducible_def equivalence : A ⊗[R] AddMonoidAlgebra R M ≃ₐ[A] AddMonoidAlgebra A M :=
  AddMonoidAlgebra.scalarTensorEquiv R A

/-- Character coefficients are mapped by the specified base algebra map. -/
theorem coeff_single (m : M) (r : R) :
    coeff R A M (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single m (algebraMap R A r) := by
  simp [coeff]

/-- Simple tensors retain their coefficient and character factors. -/
theorem equivalence_tmul (a : A) (p : AddMonoidAlgebra R M) :
    equivalence R A M (a ⊗ₜ[R] p) = a • coeff R A M p := by
  rw [equivalence_def]
  exact AddMonoidAlgebra.scalarTensorEquiv_tmul a p

/-- The coefficient projection is the usual scalar inclusion in the character ring. -/
theorem equivalence_left (a : A) :
    equivalence R A M (a ⊗ₜ[R] 1) = algebraMap A (AddMonoidAlgebra A M) a := by
  rw [equivalence_tmul, map_one, Algebra.smul_def, mul_one]

/-- The other projection is the original coefficient-change map on characters. -/
theorem equivalence_right (p : AddMonoidAlgebra R M) :
    equivalence R A M (1 ⊗ₜ[R] p) = coeff R A M p := by
  rw [equivalence_tmul, one_smul]

/-- Every character of the extended ring retains its explicit tensor representative. -/
theorem equivalence_symm_single (m : M) (a : A) :
    (equivalence R A M).symm (AddMonoidAlgebra.single m a) =
      a ⊗ₜ[R] AddMonoidAlgebra.single m 1 := by
  rw [equivalence_def]
  exact AddMonoidAlgebra.scalarTensorEquiv_symm_single m a

end FLT.Mazur.CharacterAlgebraScalarExtension
