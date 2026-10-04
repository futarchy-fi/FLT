/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatCoverDiscrepancyCocycle

/-! # The actual discrepancy is a cotangent-valued Amitsur cocycle -/

@[expose] public noncomputable section
open scoped TensorProduct
open ThreeAdicPlan.PDivisibleSystem
namespace HopfAlgebra
variable {R A B C D : Type} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [HopfAlgebra R A] [Algebra R B]
  [Algebra B C] [Algebra R C] [IsScalarTower R B C]
  [Algebra B D] [Algebra R D] [IsScalarTower R B D] [Module.Flat B D]
  (hq : Function.Surjective (algebraMap B C))
  (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (x : A →ₐ[R] C) (y : A →ₐ[R] D)
  (hy : (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
    (Algebra.TensorProduct.includeRight.restrictScalars R).comp x)

/-- The actual double-overlap discrepancy in the tensor module of the original kernel. -/
def coverPointCotangentDiscrepancy :
    (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[R]
      D ⊗[B] (D ⊗[B] RingHom.ker (algebraMap B C)) :=
  ((Algebra.doubleCoverKernelEquiv B C D).symm.toLinearMap.restrictScalars R).comp
    ((Bialgebra.counitAlgHom R A).augmentationPointCotangentEquiv
      (coverPointReduction (R := R) (B := B) (C := C) (D := D ⊗[B] D))
      (Algebra.squareZero_coverReduction B C _ hq hJ)
      ⟨coverPointDiscrepancy (B := B) y,
        pointDifference_reduction _ _ _ (Algebra.cover_point_overlap_reduction x y hy)⟩)

/-- Its coordinates are precisely the original discrepancy minus the counit. -/
theorem coverPointCotangentDiscrepancy_projection (a : A) :
    (Algebra.coverKernelInclusion B C D).lTensor D
      (coverPointCotangentDiscrepancy hq hJ x y hy
        ((Bialgebra.counitAlgHom R A).augmentationCotangent a)) =
      coverPointDiscrepancy (B := B) y a -
        algebraMap R (D ⊗[B] D) (Bialgebra.counitAlgHom R A a) := by
  rw [← Algebra.doubleCoverKernelEquiv_coe]
  change ((Algebra.doubleCoverKernelEquiv B C D)
    ((Algebra.doubleCoverKernelEquiv B C D).symm _) : D ⊗[B] D) = _
  rw [LinearEquiv.apply_symm_apply]
  exact AlgHom.augmentationPointCotangentEquiv_projection _ _ _ _ a

/-- The cocycle condition follows from the actual triple-overlap identity. -/
theorem coverPointCotangentDiscrepancy_cocycle
    (a : (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent) :
    Algebra.Amitsur.d₁ B D _ (coverPointCotangentDiscrepancy hq hJ x y hy a) = 0 := by
  obtain ⟨b, rfl⟩ := (RingHom.ker (Bialgebra.counitAlgHom R A)).toCotangent_surjective a
  rw [← AlgHom.augmentationCotangent_of_mem]
  apply Algebra.tripleCoverKernelInclusion_injective B C D
  rw [map_zero, Algebra.coverKernelInclusion_d₁, coverPointCotangentDiscrepancy_projection]
  simp only [map_sub]
  rw [show Algebra.overlapCoface₀ B D (algebraMap R _ (Bialgebra.counitAlgHom R A b)) =
      algebraMap R _ (Bialgebra.counitAlgHom R A b) from
      ((Algebra.overlapCoface₀ B D).restrictScalars R).commutes _,
    show Algebra.overlapCoface₁ B D (algebraMap R _ (Bialgebra.counitAlgHom R A b)) =
      algebraMap R _ (Bialgebra.counitAlgHom R A b) from
      ((Algebra.overlapCoface₁ B D).restrictScalars R).commutes _,
    show Algebra.overlapCoface₂ B D (algebraMap R _ (Bialgebra.counitAlgHom R A b)) =
      algebraMap R _ (Bialgebra.counitAlgHom R A b) from
      ((Algebra.overlapCoface₂ B D).restrictScalars R).commutes _]
  linear_combination coverPointDiscrepancy_cocycle hq hJ x y hy b

end HopfAlgebra
