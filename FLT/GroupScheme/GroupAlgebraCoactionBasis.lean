/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CoactionBasisProjectors
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The standard group-algebra basis for coaction projectors

The diagonal and augmentation used by the coefficient projector construction
are exactly the existing group-algebra comultiplication and counit.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace CoactionBasis

variable {R G : Type*} [CommRing R] [Monoid G]

/-- The identity standard basis vector is the group-algebra unit. -/
theorem groupAlgebraBasis_one : MonoidAlgebra.basis G R (1 : G) = 1 := by
  simp [MonoidAlgebra.basis_apply, MonoidAlgebra.one_def]

/-- The standard basis respects multiplication of degrees. -/
theorem groupAlgebraBasis_mul (i j : G) :
    MonoidAlgebra.basis G R (i * j) = MonoidAlgebra.basis G R i *
      MonoidAlgebra.basis G R j := by
  simp [MonoidAlgebra.basis_apply, MonoidAlgebra.single_mul_single]

omit [Monoid G] in
/-- Diagonal comultiplication is the actual group-algebra coalgebra operation. -/
theorem groupAlgebraBasis_diagonal :
    diagonal (MonoidAlgebra.basis G R) = Coalgebra.comul := by
  apply (MonoidAlgebra.basis G R).ext
  intro i
  rw [diagonal_basis]
  simpa only [MonoidAlgebra.basis_apply] using
    (MonoidAlgebra.isGroupLikeElem_single_one (R := R) (A := R) i).comul_eq_tmul_self.symm

omit [Monoid G] in
/-- Augmentation is the actual group-algebra counit. -/
theorem groupAlgebraBasis_augmentation :
    augmentation (MonoidAlgebra.basis G R) = Coalgebra.counit := by
  apply (MonoidAlgebra.basis G R).ext
  intro i
  rw [augmentation_basis]
  simp [MonoidAlgebra.basis_apply]

end CoactionBasis
