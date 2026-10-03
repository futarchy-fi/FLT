/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Etale.Field

/-!
# A finite ambient bound for integral model coordinates

The integral closure of an integrally closed Noetherian domain in a finite
étale generic algebra is finite. Decompose the algebra into finite separable
fields and embed its integral closure into the product of their integral closures.
-/

@[expose] public noncomputable section

namespace RaynaudParameters

/-- Integral closure is finite also for an étale algebra that is not a field.
This bounds all integral model coordinate images independently of presentations. -/
theorem finite_integralClosure_of_etale (R K A : Type*)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A] : Module.Finite R (integralClosure R A) := by
  obtain ⟨I, hI, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  let : ∀ i, Module.Finite K (L i) := fun i ↦ (hfin i).1
  let : ∀ i, Algebra.IsSeparable K (L i) := fun i ↦ (hfin i).2
  let : ∀ i, Algebra R (L i) := fun i ↦ ((algebraMap K (L i)).comp (algebraMap R K)).toAlgebra
  let : ∀ i, IsScalarTower R K (L i) := fun _ ↦ .of_algebraMap_eq fun _ ↦ rfl
  let : ∀ i, Module.Finite R (integralClosure R (L i)) := fun i ↦
    IsIntegralClosure.finite R K (L i) (integralClosure R (L i))
  let g (i : I) : A →ₐ[R] L i := ((Pi.evalAlgHom K L i).comp e.toAlgHom).restrictScalars R
  let f : integralClosure R A →ₐ[R] Π i, integralClosure R (L i) := AlgHom.pi fun i ↦
    ((g i).comp (integralClosure R A).val).codRestrict _ fun x ↦ x.2.map (g i)
  apply Module.Finite.of_injective f.toLinearMap
  intro x y h
  apply Subtype.ext
  apply e.injective
  funext i
  exact congrArg (fun z : Π i, integralClosure R (L i) ↦ (z i).1) h

end RaynaudParameters
