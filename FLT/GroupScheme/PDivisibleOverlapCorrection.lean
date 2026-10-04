/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatCoverCotangentDiscrepancy
public import FLT.GroupScheme.FlatCoverAugmentationMap
public import FLT.GroupScheme.InfinitesimalPointCorrection
public import FLT.GroupScheme.PDivisibleInfinitesimalCorrection

/-! # Apply cotangent correction to the actual local-point discrepancy -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C D : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
  [Algebra B D] [Algebra R D] [IsScalarTower R B D] [Module.FaithfullyFlat B D]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- W41's correction theorem supplies an actual point whose discrepancy is exactly that of
this local lift. Its cocycle hypothesis is proved from the actual triple overlap. -/
theorem exists_cover_discrepancy_correction
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (n : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[R] C) (y : (X.level n).CoordinateRing →ₐ[R] D)
    (hy : (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
      (Algebra.TensorProduct.includeRight.restrictScalars R).comp x) :
    ∃ c : X.LevelInfinitesimalKernel
        (coverPointReduction (R := R) (B := B) (C := C) (D := D)) n,
      HopfAlgebra.coverPointDiscrepancy (B := B) y =
        HopfAlgebra.coverPointDiscrepancy (B := B) c.val := by
  let ε := Bialgebra.counitAlgHom R (X.level n).CoordinateRing
  let q := coverPointReduction (R := R) (B := B) (C := C) (D := D)
  have hD : RingHom.ker q ^ 2 = ⊥ := Algebra.squareZero_coverReduction B C D hq hJ
  let z := HopfAlgebra.coverPointCotangentDiscrepancy hq hJ x y hy
  obtain ⟨c, hc⟩ := X.exists_original_infinitesimal_correction hq hJ n z
    (HopfAlgebra.coverPointCotangentDiscrepancy_cocycle hq hJ x y hy)
  refine ⟨c, ?_⟩
  ext a
  have he := congrArg ((Algebra.coverKernelInclusion B C D).lTensor D)
    (hc (ε.augmentationCotangent a))
  rw [Algebra.coverKernelInclusion_d₀] at he
  have hv : Algebra.coverKernelInclusion B C D
      ((Algebra.flatCoverReductionKernelEquiv B C D).symm
        ((ε.augmentationPointCotangentEquiv q hD c) (ε.augmentationCotangent a))) =
        c.val a - algebraMap R D (ε a) := by
    change ((Algebra.flatCoverReductionKernelEquiv B C D)
      ((Algebra.flatCoverReductionKernelEquiv B C D).symm _) : D) = _
    exact (congrArg Subtype.val
      ((Algebra.flatCoverReductionKernelEquiv B C D).apply_symm_apply _)).trans
        (ε.augmentationPointCotangentEquiv_projection q hD c a)
  rw [hv, HopfAlgebra.coverPointCotangentDiscrepancy_projection] at he
  let cl := ε.coverAugmentationPointMap (Algebra.TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] D) c
  let cr := ε.coverAugmentationPointMap (Algebra.TensorProduct.includeRight : D →ₐ[B] D ⊗[B] D) c
  have hd := HopfAlgebra.augmentation_pointDifference_sub_counit
    (coverPointReduction (R := R) (B := B) (C := C) (D := D ⊗[B] D))
    (Algebra.squareZero_coverReduction B C _ hq hJ) cl cr a
  change HopfAlgebra.coverPointDiscrepancy (B := B) c.val a - algebraMap R _ (ε a) =
    1 ⊗ₜ[B] c.val a - c.val a ⊗ₜ[B] 1 at hd
  have hs : (1 : D) ⊗ₜ[B] algebraMap R D (ε a) = algebraMap R D (ε a) ⊗ₜ[B] (1 : D) := by
    rw [IsScalarTower.algebraMap_apply R B D]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap R B (ε a))).symm
  simp only [TensorProduct.tmul_sub, TensorProduct.sub_tmul] at he
  rw [hs] at he
  linear_combination -he - hd

end ThreeAdicPlan.PDivisibleSystem
