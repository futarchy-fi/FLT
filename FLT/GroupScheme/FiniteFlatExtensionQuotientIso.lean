/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FiniteFlatExtensionKernelIso

/-!
# Replacing the quotient of an integral extension

An integral isomorphism of quotient models transports faithful flatness by
scalar restriction. The corresponding change of tensor base transports the
torsor comparison while keeping its prescribed second coordinate.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R : Type} [CommRing R]

/-- Faithful flatness is preserved when the source of an algebra map is replaced
by an isomorphic algebra. -/
theorem faithfullyFlatCompEquiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] A) (e : C ≃ₐ[R] B)
    (hf : letI := f.toRingHom.toAlgebra; Module.FaithfullyFlat B A) :
    letI := (f.comp e.toAlgHom).toRingHom.toAlgebra; Module.FaithfullyFlat C A := by
  let oldAlgebra : Algebra B A := f.toRingHom.toAlgebra
  let newAlgebra : Algebra C A := (f.comp e.toAlgHom).toRingHom.toAlgebra
  let baseAlgebra : Algebra C B := e.toAlgHom.toRingHom.toAlgebra
  let baseTower : IsScalarTower C B A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let oldFaithfullyFlat : Module.FaithfullyFlat B A := hf
  let baseFaithfullyFlat : Module.FaithfullyFlat C B :=
    Module.FaithfullyFlat.of_linearEquiv C C
      (AlgEquiv.ofBijective (Algebra.ofId C B) e.bijective).toLinearEquiv.symm
  exact Module.FaithfullyFlat.trans C B A

/-- Changing an isomorphic tensor base fixes every pure tensor. -/
def tensorBaseEquiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] A) (e : C ≃ₐ[R] B) :
    letI := f.toRingHom.toAlgebra
    letI := (f.comp e.toAlgHom).toRingHom.toAlgebra
    A ⊗[C] A ≃ₐ[A] A ⊗[B] A := by
  let oldAlgebra : Algebra B A := f.toRingHom.toAlgebra
  let newAlgebra : Algebra C A := (f.comp e.toAlgHom).toRingHom.toAlgebra
  let baseAlgebra : Algebra C B := e.toAlgHom.toRingHom.toAlgebra
  let baseTower : IsScalarTower C B A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let compatible : TensorProduct.CompatibleSMul C B A A :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective A A e.surjective
  exact Algebra.TensorProduct.equivOfCompatibleSMul B C A A A

/-- The tensor-base equivalence preserves the two coordinates. -/
theorem tensorBaseEquivTmul {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] A) (e : C ≃ₐ[R] B) (a b : A) :
    letI := f.toRingHom.toAlgebra
    letI := (f.comp e.toAlgHom).toRingHom.toAlgebra
    tensorBaseEquiv f e (a ⊗ₜ[C] b) = a ⊗ₜ[B] b := rfl

variable [Algebra R ℚ]

/-- Replace the quotient through an integral isomorphism, retaining exactness,
faithful flatness, and the prescribed integral torsor comparison. -/
def FiniteFlatExtension.transportQuotient {A H Q T : FiniteFlatObject R}
    (E : FiniteFlatExtension A H Q) (e : Q.Iso T) : FiniteFlatExtension A H T where
  inclusion := E.inclusion
  quotient := E.quotient.comp e.toBialgHom
  compositionZero := by
    change (E.inclusion.toAlgHom.comp E.quotient.toAlgHom).comp e.toAlgEquiv.toAlgHom = _
    rw [E.compositionZero]
    ext x
    exact congrArg (algebraMap R A.model.CoordinateRing)
      (CoalgHomClass.counit_comp_apply e x)
  pointsInjective := E.pointsInjective
  pointsSurjective := by
    intro t
    obtain ⟨q, hq⟩ := (FiniteFlatObject.pointMap_bijective e).2 t
    obtain ⟨h, hh⟩ := E.pointsSurjective q
    exact ⟨h, by rw [FiniteFlatObject.pointMap_comp, hh, hq]⟩
  pointsExact := by
    intro h
    rw [FiniteFlatObject.pointMap_comp]
    have he : FiniteFlatObject.pointMap e.toBialgHom
        (FiniteFlatObject.pointMap E.quotient h) = 0 ↔
        FiniteFlatObject.pointMap E.quotient h = 0 := by
      rw [← map_zero (FiniteFlatObject.pointMap e.toBialgHom),
        (FiniteFlatObject.pointMap_bijective e).1.eq_iff]
    exact he.trans (E.pointsExact h)
  quotientFaithfullyFlat := faithfullyFlatCompEquiv E.quotient.toAlgHom
    e.toAlgEquiv E.quotientFaithfullyFlat
  torsorEquiv := (tensorBaseEquiv E.quotient.toAlgHom e.toAlgEquiv).trans E.torsorEquiv
  torsorEquivSecond := by
    intro b
    change E.torsorEquiv (tensorBaseEquiv E.quotient.toAlgHom e.toAlgEquiv _) = _
    exact E.torsorEquivSecond b

end ThreeAdicPlan
