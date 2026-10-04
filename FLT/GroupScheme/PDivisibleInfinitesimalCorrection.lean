/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleInfinitesimalFlatCover
public import FLT.GroupScheme.CotangentAmitsurExact

/-! # Cotangent cocycles give correcting points at an original finite level -/

@[expose] public noncomputable section
open TensorProduct Algebra.Amitsur
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C D : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [CommRing D] [Algebra R B] [Algebra R D]
  [Algebra B C] [Algebra B D] [IsScalarTower R B D]
  [Module.FaithfullyFlat B D] (X : PDivisibleSystem R K p height)

/-- Every cotangent cocycle has an actual correcting point on the specified original level. -/
theorem exists_original_infinitesimal_correction
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (r : ℕ)
    (z : X.LevelCotangent r →ₗ[R] D ⊗[B] (D ⊗[B] RingHom.ker (algebraMap B C)))
    (hz : ∀ a, d₁ B D _ (z a) = 0) :
    ∃ y : X.LevelInfinitesimalKernel
        (coverPointReduction (R := R) (B := B) (C := C) (D := D)) r,
      ∀ a, d₀ B D _ ((Algebra.flatCoverReductionKernelEquiv B C D).symm
        ((AlgHom.augmentationPointCotangentEquiv _
          (coverPointReduction (R := R) (B := B) (C := C) (D := D))
          (Algebra.squareZero_coverReduction B C D hq hJ) y) a)) = z a := by
  let : Module.Free R (X.level r).CoordinateRing := Module.free_of_flat_of_isLocalRing
  let ε := Bialgebra.counitAlgHom R (X.level r).CoordinateRing
  obtain ⟨w, hw⟩ := ε.exists_cotangent_cocycle_correction z hz
  let eK := (Algebra.flatCoverReductionKernelEquiv B C D).restrictScalars R
  let f : X.LevelCotangent r →ₗ[R]
      RingHom.ker (coverPointReduction (R := R) (B := B) (C := C) (D := D)) :=
    eK.toLinearMap.comp w
  let e := AlgHom.augmentationPointCotangentEquiv ε
    (coverPointReduction (R := R) (B := B) (C := C) (D := D))
    (Algebra.squareZero_coverReduction B C D hq hJ)
  refine ⟨e.symm f, fun a ↦ ?_⟩
  change d₀ B D _ ((Algebra.flatCoverReductionKernelEquiv B C D).symm
    (e (e.symm f) a)) = z a
  rw [Equiv.apply_symm_apply]
  change d₀ B D _ ((Algebra.flatCoverReductionKernelEquiv B C D).symm
    (Algebra.flatCoverReductionKernelEquiv B C D (w a))) = z a
  rw [LinearEquiv.symm_apply_apply]
  exact hw a

end ThreeAdicPlan.PDivisibleSystem
