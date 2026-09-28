/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalEtalePoint
public import FLT.GroupScheme.LocalFiniteFlatExtension
public import FLT.GroupScheme.PadicIdentityComponentModel

/-!
# Splitting extensions with étale kernel and connected three-adic quotient

The prescribed quotient restricts to an isomorphism on the identity component.
Its inverse, followed by the identity-component inclusion, is an integral
section of the prescribed quotient map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

attribute [local instance] threeAdicFiniteFlat_henselian threeAdicSpecialFiber_artinian

/-- Quotients by complementary idempotents are formally étale over the original ring. -/
theorem formallyEtale_quotient_complement_idempotent
    {A : Type*} [CommRing A] {e : A} (he : IsIdempotentElem e) :
    Algebra.FormallyEtale A (A ⧸ Ideal.span {1 - e}) := by
  apply (Algebra.FormallyEtale.iff_of_surjective Ideal.Quotient.mk_surjective).mpr
  change IsIdempotentElem (RingHom.ker (Ideal.Quotient.mk (Ideal.span {1 - e})))
  rw [Ideal.mk_ker]
  change Ideal.span {1 - e} * Ideal.span {1 - e} = Ideal.span {1 - e}
  rw [Ideal.span_singleton_mul_span_singleton, he.one_sub.eq]

namespace ModelExtension

variable {A X Q : FF ℤ_[3] ℚ_[3]} (E : ModelExtension A X Q)

/-- Restrict the prescribed quotient to the identity component. -/
def identityComponentRestriction : ModelHom X.identityComponent Q :=
  X.identityComponentInclusion.comp E.quotient

/-- With étale kernel and local quotient coordinates, the restriction to the
identity component is a bijection on coordinate algebras. -/
theorem identityComponentRestriction_bijective_of_local
    [Algebra.Etale ℤ_[3] A.CoordinateRing] [IsLocalRing Q.CoordinateRing] :
    Function.Bijective E.identityComponentRestriction := by
  let : Algebra Q.CoordinateRing X.CoordinateRing := E.quotient.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower ℤ_[3] Q.CoordinateRing X.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.quotient.toAlgHom.comp_algebraMap.symm
  let : Module.Finite Q.CoordinateRing (X.ComponentAlgebra X.identityComponentIndex) :=
    Module.Finite.of_restrictScalars_finite ℤ_[3] Q.CoordinateRing _
  let : Algebra.Etale Q.CoordinateRing X.CoordinateRing := E.quotient_etale
  let : Algebra.FormallyEtale X.CoordinateRing (X.ComponentAlgebra X.identityComponentIndex) :=
    formallyEtale_quotient_complement_idempotent (componentIdempotent_isIdempotent _ _)
  let : Algebra.FormallyEtale Q.CoordinateRing (X.ComponentAlgebra X.identityComponentIndex) :=
    Algebra.FormallyEtale.comp Q.CoordinateRing X.CoordinateRing
      (X.ComponentAlgebra X.identityComponentIndex)
  let : IsNoetherianRing Q.CoordinateRing := IsNoetherianRing.of_finite ℤ_[3] Q.CoordinateRing
  let : Algebra.Etale Q.CoordinateRing (X.ComponentAlgebra X.identityComponentIndex) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  change Function.Bijective (algebraMap Q.CoordinateRing
    (X.ComponentAlgebra X.identityComponentIndex))
  exact algebraMap_bijective_of_local_etale_point X.identityComponentCounit

/-- If the kernel is étale and the quotient is connected, the prescribed quotient
restricts to an isomorphism on the identity component. -/
theorem identityComponentRestriction_bijective
    [Algebra.Etale ℤ_[3] A.CoordinateRing]
    (hQ : ∀ d : Q.CoordinateRing, IsIdempotentElem d → d = 0 ∨ d = 1) :
    Function.Bijective E.identityComponentRestriction := by
  let : Nontrivial Q.CoordinateRing :=
    (Bialgebra.counitAlgHom ℤ_[3] Q.CoordinateRing).toRingHom.domain_nontrivial
  let : IsLocalRing Q.CoordinateRing :=
    isLocalRing_of_henselian_idempotent_trivial (threeAdicSpecialIdeal _) hQ
  exact E.identityComponentRestriction_bijective_of_local

/-- The restricted projection as a bialgebra equivalence, with its original map retained. -/
def identityComponentRestrictionEquiv
    [Algebra.Etale ℤ_[3] A.CoordinateRing]
    (hQ : ∀ d : Q.CoordinateRing, IsIdempotentElem d → d = 0 ∨ d = 1) :
    Q.CoordinateRing ≃ₐc[ℤ_[3]] X.identityComponent.CoordinateRing :=
  BialgEquiv.ofBijective E.identityComponentRestriction
    (E.identityComponentRestriction_bijective hQ)

/-- The integral section obtained by inverting the restriction and including the component. -/
def connectedEtaleSection
    [Algebra.Etale ℤ_[3] A.CoordinateRing]
    (hQ : ∀ d : Q.CoordinateRing, IsIdempotentElem d → d = 0 ∨ d = 1) : ModelHom Q X :=
  (E.identityComponentRestrictionEquiv hQ).symm.toBialgHom.comp X.identityComponentInclusion

/-- The constructed section splits the prescribed integral quotient map. -/
theorem connectedEtaleSection_comp_quotient
    [Algebra.Etale ℤ_[3] A.CoordinateRing]
    (hQ : ∀ d : Q.CoordinateRing, IsIdempotentElem d → d = 0 ∨ d = 1) :
    (E.connectedEtaleSection hQ).comp E.quotient = BialgHom.id ℤ_[3] Q.CoordinateRing := by
  ext q
  exact (E.identityComponentRestrictionEquiv hQ).symm_apply_apply q

end ModelExtension

end ThreeAdicPlan
