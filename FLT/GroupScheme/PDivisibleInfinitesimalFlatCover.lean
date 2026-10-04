/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleInfinitesimalColimit
public import FLT.GroupScheme.RelativeFlatCotangent
public import FLT.GroupScheme.FlatCoverSquareZero

/-! # A tensor module represents the actual colimit infinitesimal kernel on flat covers -/

@[expose] public noncomputable section
open TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C D : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [CommRing D] [Algebra R B] [Algebra R C] [Algebra R D]
  [Algebra B C] [Algebra B D] [IsScalarTower R B C] [IsScalarTower R B D]
  [Module.Flat B D] (X : PDivisibleSystem R K p height)

/-- The actual cover reduction, retaining the original base-algebra structure. -/
abbrev coverPointReduction : D →ₐ[R] D ⊗[B] C :=
  (Algebra.TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C).restrictScalars R

/-- The actual colimit kernel on a flat B-cover is the original cotangent tensor module. -/
def infinitesimalFlatCoverEquiv (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (r : ℕ)
    (hM : ∀ a : RingHom.ker (algebraMap B C), p ^ r • a = 0) :
    X.InfinitesimalColimit (coverPointReduction (R := R) (B := B) (C := C) (D := D)) ≃
      D ⊗[B] (X.LevelCotangent r →ₗ[R] RingHom.ker (algebraMap B C)) := by
  let : Module.Free R (X.level r).CoordinateRing := Module.free_of_flat_of_isLocalRing
  let eK : D ⊗[B] RingHom.ker (algebraMap B C) ≃ₗ[R]
      RingHom.ker (coverPointReduction (R := R) (B := B) (C := C) (D := D)) :=
    (Algebra.flatCoverReductionKernelEquiv B C D).restrictScalars R
  let eH : (X.LevelCotangent r →ₗ[R] D ⊗[B] RingHom.ker (algebraMap B C)) ≃ₗ[R]
      (X.LevelCotangent r →ₗ[R]
        RingHom.ker (coverPointReduction (R := R) (B := B) (C := C) (D := D))) :=
    LinearEquiv.congrRight eK
  let eT : D ⊗[B] (X.LevelCotangent r →ₗ[R] RingHom.ker (algebraMap B C)) ≃ₗ[B]
      (X.LevelCotangent r →ₗ[R] D ⊗[B] RingHom.ker (algebraMap B C)) :=
    AlgHom.relativeFlatCotangentHomEquiv (Bialgebra.counitAlgHom R (X.level r).CoordinateRing)
  exact (X.infinitesimalColimitCotangentEquiv
      (coverPointReduction (R := R) (B := B) (C := C) (D := D))
    (Algebra.squareZero_coverReduction B C D hq hJ) r
    (Algebra.nsmul_coverReduction_kernel B C D (p ^ r) hM)).trans
      (eH.symm.toEquiv.trans eT.symm.toEquiv)

omit [Algebra R C] [IsScalarTower R B C] in
/-- Pure tensors give the same actual level-r cotangent functional in the cover kernel. -/
theorem infinitesimalFlatCoverEquiv_pairing
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (r : ℕ)
    (hM : ∀ a : RingHom.ker (algebraMap B C), p ^ r • a = 0)
    (d : D) (f : X.LevelCotangent r →ₗ[R] RingHom.ker (algebraMap B C))
    (a : X.LevelCotangent r) :
    X.infinitesimalColimitCotangentEquiv
      (coverPointReduction (R := R) (B := B) (C := C) (D := D))
      (Algebra.squareZero_coverReduction B C D hq hJ) r
      (Algebra.nsmul_coverReduction_kernel B C D (p ^ r) hM)
      ((X.infinitesimalFlatCoverEquiv hq hJ r hM).symm (d ⊗ₜ[B] f)) a =
        Algebra.flatCoverReductionKernelEquiv B C D (d ⊗ₜ[B] f a) := by
  let : Module.Free R (X.level r).CoordinateRing := Module.free_of_flat_of_isLocalRing
  simp only [infinitesimalFlatCoverEquiv, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply, LinearEquiv.toEquiv_symm, Equiv.symm_symm,
    LinearEquiv.coe_toEquiv]
  change Algebra.flatCoverReductionKernelEquiv B C D
    ((Bialgebra.counitAlgHom R (X.level r).CoordinateRing).relativeFlatCotangentHomEquiv
      (d ⊗ₜ[B] f) a) = _
  rw [AlgHom.relativeFlatCotangentHomEquiv_tmul]

end ThreeAdicPlan.PDivisibleSystem
