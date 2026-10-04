/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointFiberTorsor
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Descent of invariant functions and units on quotient fibres

The constructed torsor comparison and faithful flatness identify the invariant
functions with the base ring. Invariant units descend as units, with no supplied
parameter. Producing a homogeneous generator of a multiplicative torsor remains
a separate step of integral Kummer extraction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open Algebra.TensorProduct
namespace HopfAlgebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]
  [Algebra B A] [IsScalarTower R B A] [Module.FaithfullyFlat B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R)

/-- Invariant functions on the actual quotient fibre are exactly base scalars. -/
theorem pointFiber_invariant_iff (a : PointFiber (A := A) p) :
    (∃ r : R, algebraMap R (PointFiber (A := A) p) r = a) ↔
      pointFiberCoaction f hf p a = a ⊗ₜ[R] (1 : A ⧸ augmentationIdeal f) := by
  have hex := Algebra.IsEffective.of_faithfullyFlat R (PointFiber (A := A) p)
  change (a ∈ Set.range (Algebra.linearMap R (PointFiber (A := A) p))) ↔ _
  rw [← hex a, includeLeftSubRight_apply, sub_eq_zero]
  constructor
  · intro h
    change pointFiberTorsorEquiv f hf p (1 ⊗ₜ[R] a) = _
    rw [← h]
    exact (pointFiberTorsorEquiv f hf p).commutes a
  · intro h
    apply (pointFiberTorsorEquiv f hf p).injective
    change pointFiberTorsorEquiv f hf p (a ⊗ₜ[R] 1) = pointFiberCoaction f hf p a
    rw [h]
    exact (pointFiberTorsorEquiv f hf p).commutes a

omit [Module.FaithfullyFlat B A] in
/-- Invariance of a unit also gives invariance of its inverse. -/
theorem pointFiber_inverse_invariant (v : (PointFiber (A := A) p)ˣ)
    (hv : pointFiberCoaction f hf p (v : PointFiber (A := A) p) =
      (v : PointFiber (A := A) p) ⊗ₜ[R] (1 : A ⧸ augmentationIdeal f)) :
    pointFiberCoaction f hf p (↑v⁻¹) =
      (↑v⁻¹ : PointFiber (A := A) p) ⊗ₜ[R] (1 : A ⧸ augmentationIdeal f) := by
  have hu : Units.map (pointFiberCoaction f hf p).toMonoidHom v =
      Units.map (includeLeft : PointFiber (A := A) p →ₐ[R]
        PointFiber (A := A) p ⊗[R] (A ⧸ augmentationIdeal f)).toMonoidHom v :=
    Units.ext hv
  have h := congrArg (fun u ↦ (u⁻¹).val) hu
  simpa using h

/-- Every invariant unit descends uniquely to an integral base unit. -/
theorem pointFiber_existsUnique_unit (v : (PointFiber (A := A) p)ˣ)
    (hv : pointFiberCoaction f hf p (v : PointFiber (A := A) p) =
      (v : PointFiber (A := A) p) ⊗ₜ[R] (1 : A ⧸ augmentationIdeal f)) :
    ∃! u : Rˣ, Units.map (algebraMap R (PointFiber (A := A) p)).toMonoidHom u = v := by
  obtain ⟨r, hr⟩ := (pointFiber_invariant_iff f hf p _).mpr hv
  obtain ⟨s, hs⟩ := (pointFiber_invariant_iff f hf p _).mpr
    (pointFiber_inverse_invariant f hf p v hv)
  have hrs : r * s = 1 := by
    apply FaithfulSMul.algebraMap_injective R (PointFiber (A := A) p)
    rw [map_mul, map_one, hr, hs]
    exact v.mul_inv
  let u : Rˣ := ⟨r, s, hrs, by rw [mul_comm, hrs]⟩
  refine ⟨u, Units.ext hr, ?_⟩
  intro w hw
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective R (PointFiber (A := A) p)
  exact (congrArg Units.val hw).trans hr.symm

omit [Module.FaithfullyFlat B A] in
/-- A homogeneous function of torsion degree has invariant nth power. -/
theorem pointFiber_pow_invariant (n : ℕ) (z : PointFiber (A := A) p)
    (t : A ⧸ augmentationIdeal f) (ht : t ^ n = 1)
    (hz : pointFiberCoaction f hf p z = z ⊗ₜ[R] t) :
    pointFiberCoaction f hf p (z ^ n) = (z ^ n) ⊗ₜ[R] (1 : A ⧸ augmentationIdeal f) := by
  rw [map_pow, hz, tmul_pow, ht]

/-- Once a homogeneous unit is constructed, its nth power gives an integral
Kummer unit by effective descent. This does not construct that generator. -/
theorem pointFiber_exists_unit_power (n : ℕ) (z : (PointFiber (A := A) p)ˣ)
    (t : A ⧸ augmentationIdeal f) (ht : t ^ n = 1)
    (hz : pointFiberCoaction f hf p (z : PointFiber (A := A) p) =
      (z : PointFiber (A := A) p) ⊗ₜ[R] t) :
    ∃! u : Rˣ, Units.map (algebraMap R (PointFiber (A := A) p)).toMonoidHom u = z ^ n :=
  pointFiber_existsUnique_unit f hf p (z ^ n) (pointFiber_pow_invariant f hf p n z t ht hz)

end HopfAlgebra
