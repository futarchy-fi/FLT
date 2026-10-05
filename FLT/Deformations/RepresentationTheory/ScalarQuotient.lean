/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep

/-! # Continuous scalar actions recovered from surjective quotients -/

@[expose] public noncomputable section
namespace GaloisRepresentation
variable {K A V : Type*} [Field K] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [AddCommGroup V] [Module A V]

/-- The character of an equivariant surjective functional is automatically continuous. -/
theorem continuous_scalar_of_quotient (ρ : GaloisRep K A V)
    (q : V →ₗ[A] A) (hq : Function.Surjective q)
    (χ : Field.absoluteGaloisGroup K →* A)
    (he : ∀ g x, q (ρ g x) = χ g * q x) : Continuous χ := by
  obtain ⟨x, hx⟩ := hq 1
  let := moduleTopology A (Module.End A V)
  let e : Module.End A V →ₗ[A] A := q.comp (LinearMap.applyₗ x)
  have hf : (fun g ↦ e (ρ g)) = χ := by
    funext g
    change q (ρ g x) = χ g
    rw [he, hx, mul_one]
  rw [← hf]
  exact (IsModuleTopology.continuous_of_linearMap e).comp ρ.continuous

/-- Scalar multiplication by a continuous character over any base field. -/
def continuousScalarGaloisRep (χ : Field.absoluteGaloisGroup K →* A)
    (hc : Continuous χ) : GaloisRep K A A :=
  letI := moduleTopology A (Module.End A A)
  letI : ContinuousAdd (Module.End A A) := ModuleTopology.continuousAdd A _
  { toMonoidHom := (Algebra.lsmul A A A).toMonoidHom.comp χ
    continuous_toFun := (IsModuleTopology.continuous_of_linearMap
      (Algebra.lsmul A A A : A →ₐ[A] Module.End A A).toLinearMap).comp hc }

/-- The constructed scalar action is the specified character, pointwise. -/
theorem continuousScalarGaloisRep_apply (χ : Field.absoluteGaloisGroup K →* A)
    (hc : Continuous χ) (g : Field.absoluteGaloisGroup K) (x : A) :
    continuousScalarGaloisRep χ hc g x = χ g * x := rfl

end GaloisRepresentation
