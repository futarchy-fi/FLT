/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupAffineQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finiteness of affine finite-group quotient maps

If the original coordinate ring is of finite type over a ring of scalars fixed
by the action, it is finite as a module over its actual invariant subring.
Consequently its affine quotient map is finite and proper. No noetherian or
freeness hypothesis is required, and the group order need not be invertible.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupQuotient

universe u

variable (G A : Type u) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  (R : Type u) [CommRing R] [Algebra R A] [SMulCommClass G R A] [Algebra.FiniteType R A]

include R in
/-- Finiteness over invariants follows from finite type over the original fixed scalars. -/
theorem inclusion_finite : (inclusion G A).Finite := by
  apply (inclusion_isIntegral G A).to_finite
  let b := lift G A (algebraMap R A) (fun g r ↦ smul_algebraMap g r)
  apply RingHom.FiniteType.of_comp_finiteType (f := b)
  change (algebraMap R A).FiniteType
  exact RingHom.finiteType_algebraMap.mpr inferInstance

include R in
/-- The actual affine quotient morphism of a finite-type algebra is finite. -/
theorem quotientMap_finite : IsFinite (quotientMap G A) :=
  (IsFinite.SpecMap_iff _).mpr (inclusion_finite G A R)

include R in
/-- Properness here is of the quotient map, not of its target over the scalar base. -/
theorem quotientMap_proper : IsProper (quotientMap G A) := by
  let _ := quotientMap_finite G A R
  infer_instance

end FLT.Mazur.FiniteGroupQuotient
