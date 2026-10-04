/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.KrullDimension.FibreFieldExtension
public import Mathlib.RingTheory.QuasiFinite.Basic

/-! # Fibre bounds at coefficient-stage primes seen by a quasi-finite base change -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [FiniteType R A] [QuasiFinite S (S ⊗[R] A)]

/-- If the final base change is quasi-finite, every stage fibre at a prime coming
from that final base is zero-dimensional. Primes outside this image are not asserted good. -/
theorem fibre_dimension_zero_of_quasiFinite_baseChange (p : Ideal S) [p.IsPrime] :
    ringKrullDim ((p.comap (algebraMap R S)).Fiber A) ≤ 0 := by
  rw [← ringKrullDim_fibre_residue_extension R S A p]
  rw [← ringKrullDim_eq_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R S p.ResidueField p.ResidueField A).toRingEquiv]
  exact (Ring.krullDimLE_iff (n := 0)).mp inferInstance

end Algebra
