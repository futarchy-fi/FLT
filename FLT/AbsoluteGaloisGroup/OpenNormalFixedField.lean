/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Realizing an open normal quotient by a finite Galois extension

The fixed field of an open normal subgroup is finite Galois. The quotient
identification agrees with restriction of automorphisms.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (N : OpenNormalSubgroup Gal(L/K))

/-- View an open normal subgroup as a closed subgroup for the Krull correspondence. -/
def openNormalClosed : ClosedSubgroup Gal(L/K) :=
  ⟨N.toSubgroup, N.toOpenSubgroup.isClosed⟩

/-- The fixing subgroup of the fixed field is the original open normal subgroup. -/
theorem fixingSubgroup_openNormal :
    (IntermediateField.fixedField N.toSubgroup).fixingSubgroup = N.toSubgroup :=
  InfiniteGalois.fixingSubgroup_fixedField (openNormalClosed N)

/-- Openness makes the fixed field finite over the base field. -/
theorem finiteDimensional_openNormal_fixedField :
    FiniteDimensional K (IntermediateField.fixedField N.toSubgroup) := by
  apply (InfiniteGalois.isOpen_iff_finite _).mp
  rw [fixingSubgroup_openNormal N]
  exact N.toOpenSubgroup.isOpen

/-- The finite Galois intermediate field attached to an open normal subgroup. -/
def openNormalFixedField : FiniteGaloisIntermediateField K L where
  toIntermediateField := IntermediateField.fixedField N.toSubgroup
  finiteDimensional := finiteDimensional_openNormal_fixedField N
  isGalois := inferInstance

/-- The abstract quotient identifies with the Galois group of the fixed field. -/
noncomputable def openNormalQuotientEquiv :
    Gal(L/K) ⧸ N.toSubgroup ≃* Gal(openNormalFixedField N/K) := by
  let : (openNormalClosed N).toSubgroup.Normal := N.isNormal'
  exact InfiniteGalois.normalAutEquivQuotient (openNormalClosed N)

/-- The quotient identification sends an automorphism to its restriction. -/
theorem openNormalQuotientEquiv_mk (g : Gal(L/K)) :
    openNormalQuotientEquiv N ⟦g⟧ = AlgEquiv.restrictNormalHom (openNormalFixedField N) g := by
  let : (openNormalClosed N).toSubgroup.Normal := N.isNormal'
  exact InfiniteGalois.normalAutEquivQuotient_apply (openNormalClosed N) g

end GaloisRepresentation.Extensions
