/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # Rational points of finite geometric fibres -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra
variable {Ω D : Type*} [Field Ω] [IsAlgClosed Ω] [CommRing D]
  [Algebra Ω D] [Module.Finite Ω D] [Nontrivial D]

/-- A nonzero finite algebra over an algebraically closed field has a rational point. -/
theorem nonempty_hom_of_finite_of_isAlgClosed : Nonempty (D →ₐ[Ω] Ω) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal D
  let := hm
  exact ⟨(IsAlgClosed.lift : (D ⧸ m) →ₐ[Ω] Ω).comp (Ideal.Quotient.mkₐ Ω m)⟩

end Algebra

namespace AlgHom
variable {R A H Ω : Type*} [CommRing R] [CommRing A] [CommRing H]
  [Field Ω] [IsAlgClosed Ω] [Algebra R A] [Algebra R H] [Algebra R Ω]

/-- Every geometric point of a finite faithfully flat affine target has a lift. -/
theorem exists_lift_of_finite_faithfullyFlat (f : A →ₐ[R] H)
    (hf : f.toRingHom.FaithfullyFlat) (hfin : f.toRingHom.Finite) (x : A →ₐ[R] Ω) :
    ∃ y : H →ₐ[R] Ω, y.comp f = x := by
  let : Algebra A H := f.toRingHom.toAlgebra
  let : Algebra A Ω := x.toRingHom.toAlgebra
  let : IsScalarTower R A H := IsScalarTower.of_algHom f
  let : IsScalarTower R A Ω := IsScalarTower.of_algHom x
  let : Module.FaithfullyFlat A H := hf
  let : Module.Finite A H := hfin
  let D := Ω ⊗[A] H
  obtain ⟨z⟩ := Algebra.nonempty_hom_of_finite_of_isAlgClosed (Ω := Ω) (D := D)
  let y : H →ₐ[R] Ω := (z.restrictScalars R).comp
    ((Algebra.TensorProduct.includeRight : H →ₐ[A] D).restrictScalars R)
  refine ⟨y, ?_⟩
  ext a
  change z (1 ⊗ₜ[A] f a) = x a
  have ht : (1 : Ω) ⊗ₜ[A] f a = x a ⊗ₜ[A] (1 : H) :=
    (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm
  rw [ht]
  exact z.commutes (x a)

end AlgHom
