/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoefficientDifferenceIdeal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Original coefficient separation implies comaximal tensor coordinate kernels

Every scalar-compatible source coordinate extends to the whole scalar tensor
product. If the original coordinate differences generate the unit ideal,
the two extended kernels are comaximal, with no reducedness assumption.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarCoordinateKernelSeparation
open FiniteCoefficientDifference
variable {R A T : Type*} [CommRing R] [CommRing A] [CommRing T]
  [Algebra R A] [Algebra R T]

/-- Extend a source coordinate along the actual test scalar map. -/
def coordinate (l : A →ₐ[R] T) : (T ⊗[R] A) →ₐ[T] T :=
  Algebra.TensorProduct.lift (AlgHom.id T T) l (fun _ _ ↦ Commute.all _ _)

/-- The extended coordinate agrees with the original map on source coefficients. -/
theorem coordinate_coefficient (l : A →ₐ[R] T) (a : A) :
    coordinate l (1 ⊗ₜ[R] a) = l a := by
  simp [coordinate]

/-- Source differences give comaximal kernels of the full tensor coordinates. -/
theorem kernels_coprime (l r : A →ₐ[R] T)
    (h : differenceIdeal l.toRingHom r.toRingHom = ⊤) :
    IsCoprime (RingHom.ker (coordinate l).toRingHom) (RingHom.ker (coordinate r).toRingHom) := by
  let K := RingHom.ker (coordinate l).toRingHom ⊔ RingHom.ker (coordinate r).toRingHom
  have hle : differenceIdeal l.toRingHom r.toRingHom ≤
      Ideal.comap (algebraMap T (T ⊗[R] A)) K := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hl : (1 ⊗ₜ[R] a) - algebraMap T (T ⊗[R] A) (l a) ∈
        RingHom.ker (coordinate l).toRingHom := by
      change coordinate l ((1 ⊗ₜ[R] a) - algebraMap T (T ⊗[R] A) (l a)) = 0
      simp only [map_sub, coordinate_coefficient, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hr : (1 ⊗ₜ[R] a) - algebraMap T (T ⊗[R] A) (r a) ∈
        RingHom.ker (coordinate r).toRingHom := by
      change coordinate r ((1 ⊗ₜ[R] a) - algebraMap T (T ⊗[R] A) (r a)) = 0
      simp only [map_sub, coordinate_coefficient, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have hm := K.sub_mem (Ideal.mem_sup_right hr) (Ideal.mem_sup_left hl)
    change algebraMap T (T ⊗[R] A) (l a - r a) ∈ K
    simpa only [map_sub, sub_sub_sub_cancel_left] using hm
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have hone : (1 : T) ∈ differenceIdeal l.toRingHom r.toRingHom := by
    rw [h]
    exact Submodule.mem_top
  have hm := hle hone
  simpa only [Ideal.mem_comap, map_one] using hm

end FLT.Mazur.ScalarCoordinateKernelSeparation
