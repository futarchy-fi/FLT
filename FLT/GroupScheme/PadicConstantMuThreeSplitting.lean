/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicConnectedEtaleSplitting
public import FLT.GroupScheme.PadicMuThreeConnected
public import Mathlib.RingTheory.Etale.Pi

/-!
# Local splitting of constant-three extensions of the cube-root group

For an actual extension in `ModelExtension`, coordinate identifications with
the constant group of order three and with `μ₃` suffice. The restriction of the
prescribed quotient to the identity component is a bialgebra equivalence;
inverting it produces an integral section, without a generic splitting input.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan.ModelExtension

variable {A X Q : FF ℤ_[3] ℚ_[3]} (E : ModelExtension A X Q)

/-- The standard cube-root coordinate identification proves connectedness of the quotient. -/
theorem muThreeCoordinates_idempotent_trivial
    (eQ : Q.CoordinateRing ≃ₐ[ℤ_[3]] PadicMuThreeAlgebra)
    (d : Q.CoordinateRing) (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  rcases padicMuThree_idempotent_trivial (eQ d) (hd.map eQ.toRingEquiv.toRingHom) with h | h
  · left
    apply eQ.injective
    simpa only [map_zero] using h
  · right
    apply eQ.injective
    simpa only [map_one] using h

/-- For an extension of `μ₃` by constant `ℤ/3`, the actual projection restricted to
the identity component is an isomorphism. The coordinate identifications impose
no section, generic splitting, or rank condition on the middle model. -/
def constantThreeMuThreeRestrictionEquiv
    (eA : A.CoordinateRing ≃ₐ[ℤ_[3]] (ZMod 3 → ℤ_[3]))
    (eQ : Q.CoordinateRing ≃ₐ[ℤ_[3]] PadicMuThreeAlgebra) :
    Q.CoordinateRing ≃ₐc[ℤ_[3]] X.identityComponent.CoordinateRing := by
  let : Algebra.Etale ℤ_[3] A.CoordinateRing := Algebra.Etale.of_equiv eA.symm
  exact E.identityComponentRestrictionEquiv (muThreeCoordinates_idempotent_trivial eQ)

/-- The equivalence is precisely the specified projection followed by the component quotient. -/
@[simp] theorem constantThreeMuThreeRestrictionEquiv_apply
    (eA : A.CoordinateRing ≃ₐ[ℤ_[3]] (ZMod 3 → ℤ_[3]))
    (eQ : Q.CoordinateRing ≃ₐ[ℤ_[3]] PadicMuThreeAlgebra) (q : Q.CoordinateRing) :
    E.constantThreeMuThreeRestrictionEquiv eA eQ q =
      X.identityComponentProjection (E.quotient q) := rfl

/-- The integral section of the prescribed quotient in a constant-three extension of `μ₃`. -/
def constantThreeMuThreeSection
    (eA : A.CoordinateRing ≃ₐ[ℤ_[3]] (ZMod 3 → ℤ_[3]))
    (eQ : Q.CoordinateRing ≃ₐ[ℤ_[3]] PadicMuThreeAlgebra) : ModelHom Q X :=
  (E.constantThreeMuThreeRestrictionEquiv eA eQ).symm.toBialgHom.comp X.identityComponentInclusion

/-- Every such local extension has an integral section of its given projection. -/
theorem constantThreeMuThreeSection_comp_quotient
    (eA : A.CoordinateRing ≃ₐ[ℤ_[3]] (ZMod 3 → ℤ_[3]))
    (eQ : Q.CoordinateRing ≃ₐ[ℤ_[3]] PadicMuThreeAlgebra) :
    (E.constantThreeMuThreeSection eA eQ).comp E.quotient =
      BialgHom.id ℤ_[3] Q.CoordinateRing := by
  ext q
  exact (E.constantThreeMuThreeRestrictionEquiv eA eQ).symm_apply_apply q

include E in
/-- The identity component of a constant-three extension of `μ₃` has rank three. -/
theorem constantThreeMuThree_identityComponent_finrank
    (eA : A.CoordinateRing ≃ₐ[ℤ_[3]] (ZMod 3 → ℤ_[3]))
    (eQ : Q.CoordinateRing ≃ₐ[ℤ_[3]] PadicMuThreeAlgebra) :
    Module.finrank ℤ_[3] X.identityComponent.CoordinateRing = 3 := by
  let e := (E.constantThreeMuThreeRestrictionEquiv eA eQ).symm.toAlgEquiv.trans eQ
  rw [e.toLinearEquiv.finrank_eq]
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (Multiplicative (ZMod 3)) ℤ_[3])]
  simp

end ThreeAdicPlan.ModelExtension
