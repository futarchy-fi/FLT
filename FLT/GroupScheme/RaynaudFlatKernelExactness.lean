/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudKernelExactness
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Exactness for flat scheme-theoretic kernels

Any flat quotient of the coordinates of a finite flat model is determined by
its geometric generic points. Consequently, once the actual quotient kernel
is flat, it agrees with the flat closure of the generic kernel. This reduction
also applies to ramified quotients; it does not assert their relative flatness.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AlgHom

variable {R D A : Type*} [CommRing R] [CommRing D] [CommRing A]
    [Algebra R D] [Algebra R A] [Algebra D A] [IsScalarTower R D A]

/-- The fibre over an augmentation of a relatively flat algebra is flat over
the augmentation's base ring. -/
theorem quotient_map_ker_flat [Module.Flat D A] (ε : D →ₐ[R] R) :
    Module.Flat R (A ⧸ (RingHom.ker ε.toRingHom).map (algebraMap D A)) := by
  let I := RingHom.ker ε.toRingHom
  have hε : Function.Surjective ε := fun r ↦ ⟨algebraMap R D r, by simp⟩
  let e : (D ⧸ I) ≃ₐ[R] R := Ideal.quotientKerAlgEquivOfSurjective hε
  let : Module.Flat R (D ⧸ I) := Module.Flat.of_linearEquiv e.toLinearEquiv
  let : Module.Flat R ((D ⧸ I) ⊗[D] A) := Module.Flat.trans R (D ⧸ I) _
  let t := ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toLinearEquiv.restrictScalars R)
    ≪≫ₗ ((Algebra.TensorProduct.comm D A (D ⧸ I)).toLinearEquiv.restrictScalars R)
  exact Module.Flat.of_linearEquiv t

end AlgHom

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsFractionRing R K] {S X Y : FF R K}

omit [PerfectField K] [IsFractionRing R K] in
/-- Every quotient of the coordinate algebra has an etale generic fibre. -/
theorem FF.quotient_genericEtale (X : FF R K) (I : Ideal X.CoordinateRing) :
    Algebra.Etale K (K ⊗[R] (X.CoordinateRing ⧸ I)) := by
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := R) K X.CoordinateRing K I
  let : Algebra.FormallyUnramified K (K ⊗[R] (X.CoordinateRing ⧸ I)) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact ⟨Algebra.FormallyEtale.of_formallyUnramified_of_field K _,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- A flat quotient of a finite flat model is detected by those geometric generic
points of the original model which annihilate its defining ideal. -/
theorem FF.mem_ideal_iff_of_flat_quotient (X : FF R K) (I : Ideal X.CoordinateRing)
    [Module.Flat R (X.CoordinateRing ⧸ I)] (a : X.CoordinateRing) :
    a ∈ I ↔ ∀ p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K,
      (∀ b ∈ I, p (1 ⊗ₜ[R] b) = 0) → p (1 ⊗ₜ[R] a) = 0 := by
  constructor
  · exact fun ha p hp ↦ hp a ha
  · intro h
    let : Algebra.Etale K (K ⊗[R] (X.CoordinateRing ⧸ I)) := X.quotient_genericEtale I
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply Algebra.TensorProduct.includeRight_injective (A := K) (IsFractionRing.injective R K)
    change (1 ⊗ₜ[R] Ideal.Quotient.mk I a : K ⊗[R] (X.CoordinateRing ⧸ I)) = 1 ⊗ₜ[R] 0
    rw [TensorProduct.tmul_zero]
    apply (InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed K (AlgebraicClosure K)
      (K ⊗[R] (X.CoordinateRing ⧸ I))).1
    ext p
    change p (1 ⊗ₜ[R] Ideal.Quotient.mk I a) = p 0
    rw [map_zero]
    let π : K ⊗[R] X.CoordinateRing →ₐ[K] K ⊗[R] (X.CoordinateRing ⧸ I) :=
      Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ R I)
    apply h (p.comp π)
    intro b hb
    change p (1 ⊗ₜ[R] Ideal.Quotient.mk I b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, TensorProduct.tmul_zero, map_zero]

variable [IsDedekindDomain R]

/-- Flatness of the actual scheme kernel identifies it with the flat closure of
any exact generic subgroup, including for ramified and nonsplit quotients. -/
theorem GenericGaloisHom.quotientKernelIdeal_eq_closureIdeal_of_flat
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    [Module.Flat R (X.CoordinateRing ⧸ q.quotientKernelIdeal)] :
    q.quotientKernelIdeal = i.closureIdeal := by
  ext a
  rw [X.mem_ideal_iff_of_flat_quotient q.quotientKernelIdeal,
    i.mem_closureIdeal_iff_vanish]
  simp only [q.quotientKernelIdeal_vanish_iff hq, hexact]

/-- Relative flatness of the source over the contracted quotient makes its
actual scheme-theoretic kernel flat over the original base. -/
theorem GenericGaloisHom.quotientKernel_flat_of_relative_flat
    (q : GenericGaloisHom X Y) [Module.Flat q.quotientCoordinates X.CoordinateRing] :
    Module.Flat R (X.CoordinateRing ⧸ q.quotientKernelIdeal) :=
  (Bialgebra.counitAlgHom R q.quotientCoordinates).quotient_map_ker_flat

/-- Relative flatness suffices for integral kernel exactness of any contracted
quotient; neither unramifiedness nor a splitting is required. -/
theorem GenericGaloisHom.quotientKernelIdeal_eq_closureIdeal_of_relative_flat
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    [Module.Flat q.quotientCoordinates X.CoordinateRing] :
    q.quotientKernelIdeal = i.closureIdeal := by
  let := q.quotientKernel_flat_of_relative_flat
  exact i.quotientKernelIdeal_eq_closureIdeal_of_flat q hq hexact

end ThreeAdicPlan
