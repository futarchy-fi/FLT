/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.OpenKernel
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Realizing finite quotients of the absolute Galois group

This proves leaf G2 of `docs/CHEBOTAREV_PLAN.md`. The fixed field of the
kernel realizes a continuous surjection onto a finite discrete group as a
finite Galois group, compatibly with restriction of automorphisms.
-/

@[expose] public section

namespace GaloisRepresentation.Chebotarev

/-- Every continuous finite discrete quotient of the absolute Galois group of
`ℚ` is the Galois group of a finite Galois intermediate field. The equivalence
intertwines restriction with the given quotient map. -/
theorem exists_finiteGalois_realization {G : Type*} [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* G) (hf : Function.Surjective f) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L)
      (e : Gal(L/ℚ) ≃* G),
        ∀ g, e (AlgEquiv.restrictNormalHom L g) = f g := by
  let H : ClosedSubgroup Gal(AlgebraicClosure ℚ/ℚ) :=
    ⟨f.toMonoidHom.ker, (isClosed_singleton.preimage f.continuous)⟩
  let L := IntermediateField.fixedField H.toSubgroup
  have hfix : L.fixingSubgroup = H.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have hopen : IsOpen L.fixingSubgroup.carrier := by
    rw [hfix]
    exact isOpen_ker f
  let : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp hopen
  let : H.Normal := inferInstanceAs f.toMonoidHom.ker.Normal
  let : IsGalois ℚ L := inferInstance
  let e := (InfiniteGalois.normalAutEquivQuotient H).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hf)
  refine ⟨L, inferInstance, inferInstance, e, fun g ↦ ?_⟩
  change (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hf)
    ((InfiniteGalois.normalAutEquivQuotient H).symm
      (AlgEquiv.restrictNormalHom L g)) = f g
  rw [← InfiniteGalois.normalAutEquivQuotient_apply H g, MulEquiv.symm_apply_apply]
  rfl

end GaloisRepresentation.Chebotarev
