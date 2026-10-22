/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFreeInvariantFiniteness
public import FLT.Mazur.ScalarOrbitQuotientComparison
public import FLT.Mazur.ScalarFiniteTypeFiberTests
public import FLT.Mazur.FiniteCokernelResidualLifting

/-!
# Constructing full scalar membership from finite residual data

For a finite original source with a free finite action, weighted trace makes
the full invariant scalar cokernel finite. Residual surjectivity over a local
scalar ring then kills that cokernel by Nakayama. This constructs exact scalar
fullness, the original orbit comparison, and rigidity at every target prime.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarOrbitTensorComparison
open FiniteGroupQuotient
variable (G R A : Type) [Group G] [Finite G] [CommRing R] [CommRing A]
  [MulSemiringAction G A] [Algebra R A] [Algebra R (invariantRing G A)]
  [IsScalarTower R (invariantRing G A) A] [Module.Finite R A] [IsLocalRing R]
local notation "S" => invariantRing G A
variable (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
  (hres : LinearMap.range (Algebra.linearMap R (invariantRing G A)) ⊔
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R (invariantRing G A)) = ⊤)
include hfree hres

/-- Finite trace coordinates upgrade residual scalar membership to actual full membership. -/
theorem invariantScalar_surjective_of_residual : Function.Surjective (algebraMap R S) := by
  let _ := invariant_finite_of_source G R A hfree
  exact FiniteErrorReduction.surjective_of_finite_residual (Algebra.linearMap R S) ⊤
    Module.Finite.fg_top (sup_top_eq _) hres

/-- The full original tensor comparison is bijective after the residual finite test. -/
theorem comparison_bijective_of_residual : Function.Bijective (comparison G R A) :=
  (fullComparison G R A hfree (invariantScalar_surjective_of_residual G R A hfree hres)).bijective

/-- Residual fullness and the constructed finite cokernel kill all full source differentials. -/
theorem formallyUnramified_of_residual : Algebra.FormallyUnramified R A := by
  let _ : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S)
      (invariantScalar_surjective_of_residual G R A hfree hres)
  let _ := invariant_formallyUnramified G A hfree
  exact Algebra.FormallyUnramified.comp R S A

/-- Every exact target prime sees zero differentials, including embedded primes. -/
theorem fiberVanishes_of_residual {B : Type} [CommRing B]
    (f : A →+* B) (Q : PrimeSpectrum B) :
    ScalarFiniteTypeFiberTests.FiberVanishes (algebraMap R A) f Q := by
  have hu : let _ := (algebraMap R A).toAlgebra; Algebra.FormallyUnramified R A := by
    rw [toAlgebra_algebraMap]
    exact formallyUnramified_of_residual G R A hfree hres
  let _ := (algebraMap R A).toAlgebra
  let _ := ((algebraMap B Q.asIdeal.ResidueField).comp f).toAlgebra
  let _ := hu
  exact inferInstanceAs (Subsingleton (TensorProduct A Q.asIdeal.ResidueField
    (KaehlerDifferential R A)))

/-- Actual source equations construct the full-stalk test from finite residual scalar data. -/
theorem stalkTest_of_residual {B : Type} [CommRing B]
    (f : A →+* B) (Q : PrimeSpectrum B) :
    ScalarStalkJacobianTests.Test (algebraMap R A) f Q := by
  apply ScalarFiniteTypeFiberTests.test _ _ _ ?_
    (fiberVanishes_of_residual G R A hfree hres f Q)
  rw [toAlgebra_algebraMap]
  infer_instance

end FLT.Mazur.ScalarOrbitTensorComparison
