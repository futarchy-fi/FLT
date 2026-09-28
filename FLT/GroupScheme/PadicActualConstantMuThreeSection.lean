/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantMuThreeGlobalSplitting
public import FLT.GroupScheme.ConstantMuThreeTorsion
public import FLT.GroupScheme.PadicConstantMuThreeSplitting
public import Mathlib.RingTheory.RingHom.Etale

/-!
# A three-adic section of the actual global extension

The original quotient is étale because its kernel is constant. This remains
true for its actual tensor map after base change. Restriction to the identity
component gives an isomorphism onto the connected cube-root quotient, hence a
section of the prescribed map. No replacement model or generic section is assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Extending the base of an étale algebra map preserves étaleness
of the actual tensor map. -/
theorem Algebra.etale_tensor_map (R A B S : Type)
    [CommRing R] [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra R S]
    (f : A →ₐ[R] B) (hf : f.toRingHom.Etale) :
    (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom.Etale := by
  let algebraAB : Algebra A B := f.toRingHom.toAlgebra
  let towerRAB : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let etaleAB : Algebra.Etale A B := hf
  let P := A ⊗[R] S
  let T := P ⊗[A] B
  let c := (Algebra.TensorProduct.comm R S A).toRingEquiv
  let e : T ≃+* S ⊗[R] B :=
    (Algebra.TensorProduct.comm A P B).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R A B B S).toRingEquiv.trans
        (Algebra.TensorProduct.comm R B S).toRingEquiv)
  have ht : (algebraMap P T).Etale := RingHom.etale_algebraMap.mpr inferInstance
  have h := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (f := c.toRingHom) c.bijective) ht)
    (RingHom.Etale.of_bijective (f := e.toRingHom) e.bijective)
  have he : e.toRingHom.comp ((algebraMap P T).comp c.toRingHom) =
      (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul s a =>
      change e ((a ⊗ₜ[R] s) ⊗ₜ[A] (1 : B)) = s ⊗ₜ[R] f a
      change s ⊗ₜ[R] (a • (1 : B)) = s ⊗ₜ[R] f a
      rw [Algebra.smul_def, mul_one]
      rfl
  rw [he] at h
  exact h

namespace ThreeAdicPlan
open scoped TensorProduct
attribute [local instance] threeAdicFiniteFlat_henselian threeAdicSpecialFiber_artinian

/-- An étale quotient with cube-root coordinates has a section on the original middle model. -/
theorem exists_section_of_etale_muThree_quotient {X Q : FF ℤ_[3] ℚ_[3]} (q : ModelHom X Q)
    (hq : q.toAlgHom.toRingHom.Etale)
    (eQ : Q.CoordinateRing ≃ₐ[ℤ_[3]] PadicMuThreeAlgebra) :
    ∃ s : ModelHom Q X, s.comp q = BialgHom.id ℤ_[3] Q.CoordinateRing := by
  let algebraQX : Algebra Q.CoordinateRing X.CoordinateRing := q.toAlgHom.toRingHom.toAlgebra
  let towerZQX : IsScalarTower ℤ_[3] Q.CoordinateRing X.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' q.toAlgHom.comp_algebraMap.symm
  let etaleQX : Algebra.Etale Q.CoordinateRing X.CoordinateRing := hq
  let nontrivialQ : Nontrivial Q.CoordinateRing :=
    (Bialgebra.counitAlgHom ℤ_[3] Q.CoordinateRing).toRingHom.domain_nontrivial
  let localQ : IsLocalRing Q.CoordinateRing :=
    isLocalRing_of_henselian_idempotent_trivial (threeAdicSpecialIdeal _)
      (ModelExtension.muThreeCoordinates_idempotent_trivial eQ)
  let finiteComponent : Module.Finite Q.CoordinateRing
      (X.ComponentAlgebra X.identityComponentIndex) :=
    Module.Finite.of_restrictScalars_finite ℤ_[3] Q.CoordinateRing _
  let formallyEtaleComponent : Algebra.FormallyEtale X.CoordinateRing
      (X.ComponentAlgebra X.identityComponentIndex) :=
    formallyEtale_quotient_complement_idempotent (componentIdempotent_isIdempotent _ _)
  let formallyEtaleQComponent : Algebra.FormallyEtale Q.CoordinateRing
      (X.ComponentAlgebra X.identityComponentIndex) :=
    Algebra.FormallyEtale.comp Q.CoordinateRing X.CoordinateRing _
  let noetherianQ : IsNoetherianRing Q.CoordinateRing :=
    IsNoetherianRing.of_finite ℤ_[3] Q.CoordinateRing
  let etaleQComponent : Algebra.Etale Q.CoordinateRing
      (X.ComponentAlgebra X.identityComponentIndex) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let r : ModelHom X.identityComponent Q := X.identityComponentInclusion.comp q
  have hr : Function.Bijective r :=
    algebraMap_bijective_of_local_etale_point X.identityComponentCounit
  let e := BialgEquiv.ofBijective r hr
  refine ⟨e.symm.toBialgHom.comp X.identityComponentInclusion, ?_⟩
  ext x
  exact e.symm_apply_apply x

/-- Three remains nonzero in the integral coefficient map from `ℤ[1/2]`. -/
local instance notThreeDvdTwo : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩

/-- The prescribed quotient of the actual extension has a section after
scalar extension to `ℤ₃`, on the original tensor-product middle model. -/
theorem FiniteFlatExtension.exists_actual_three_adic_section
    {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree) :
    ∃ s : ModelHom (muThree.toFF.scalarExtension ℤ_[3] ℚ_[3])
        (X.toFF.scalarExtension ℤ_[3] ℚ_[3]),
      s.comp (ModelHom.scalarExtension ℤ_[3] ℚ_[3]
        (X := X.toFF) (Y := muThree.toFF) E.quotient) =
          BialgHom.id ℤ_[3] (muThree.toFF.scalarExtension ℤ_[3] ℚ_[3]).CoordinateRing := by
  let etaleKernel : Algebra.Etale ZInvTwo constantThree.model.CoordinateRing := constantThree_etale
  let q : ModelHom (X.toFF.scalarExtension ℤ_[3] ℚ_[3])
      (muThree.toFF.scalarExtension ℤ_[3] ℚ_[3]) :=
    ModelHom.scalarExtension ℤ_[3] ℚ_[3] (X := X.toFF) (Y := muThree.toFF) E.quotient
  have hq : q.toAlgHom.toRingHom.Etale :=
    Algebra.etale_tensor_map ZInvTwo muThree.model.CoordinateRing X.model.CoordinateRing
      ℤ_[3] E.quotient.toAlgHom E.quotient_etale
  exact exists_section_of_etale_muThree_quotient q hq
    (MonoidAlgebra.scalarTensorEquiv ZInvTwo ℤ_[3] (M := Multiplicative (ZMod 3)))

end ThreeAdicPlan
