/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentKernelLifting
public import FLT.Mathlib.RingTheory.SplitSquareZeroTest

/-! # Lifting module-valued functionals by actual split test algebras -/

@[expose] public noncomputable section
open scoped SplitSquareZeroTest
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K S M N : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]

/-- Every functional into a quotient module over a p-nilpotent test ring lifts.
This follows from the proved formal smoothness of the original point functor. -/
theorem exists_cotangent_functional_lift (hS : IsNilpotent (p : S))
    (f : M →ₗ[S] N) (hf : Function.Surjective f) (φ : X.cotangentLimit →ₗ[R] N) :
    ∃ ψ : X.cotangentLimit →ₗ[R] M, (f.restrictScalars R).comp ψ = φ := by
  let q := TrivSqZeroExt.fstHom R S M
  let q' := TrivSqZeroExt.fstHom R S N
  let β := (TrivSqZeroExt.map f).restrictScalars R
  have hc : q'.comp β = (AlgHom.id R S).comp q := by
    apply AlgHom.ext
    intro x
    exact TrivSqZeroExt.fst_map f x
  let eM := SplitSquareZeroTest.kernelEquiv (R := R) (S := S) (M := M)
  let eN := SplitSquareZeroTest.kernelEquiv (R := R) (S := S) (M := N)
  obtain ⟨r, hr⟩ := hS
  have hN (b : RingHom.ker q') : p ^ r • b = 0 := by
    apply eN.injective
    rw [map_nsmul, map_zero]
    change p ^ r • eN b = 0
    rw [← Nat.cast_smul_eq_nsmul S, Nat.cast_pow, hr, zero_smul]
  obtain ⟨g, hg⟩ := X.exists_cotangent_kernel_lift q q' β hc
    (SplitSquareZeroTest.map_surjective f hf) (SplitSquareZeroTest.map_kernel_sq f)
    (SplitSquareZeroTest.natCast_nilpotent (M := M) p ⟨r, hr⟩)
    (SplitSquareZeroTest.kernel_sq (R := R)) (SplitSquareZeroTest.kernel_sq (R := R))
    r hN (eN.symm.toLinearMap.comp φ)
  refine ⟨eM.toLinearMap.comp g, ?_⟩
  ext x
  have hx := congrArg eN (LinearMap.congr_fun hg x)
  change (TrivSqZeroExt.map f (g x)).snd = eN (eN.symm (φ x)) at hx
  change f (g x).val.snd = φ x
  simpa only [TrivSqZeroExt.snd_map, LinearEquiv.apply_symm_apply] using hx

end ThreeAdicPlan.PDivisibleSystem
