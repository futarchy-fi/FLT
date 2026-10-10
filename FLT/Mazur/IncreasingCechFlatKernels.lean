/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatCokernelStep
public import FLT.Mazur.IncreasingCechZeroSections

/-!
# Flat kernels of the actual bounded Cech complex

Flat terms and flat positive cohomology imply flat kernels, by descending
from the cardinal bound. In degree zero this proves flatness of actual global
sections; no flatness of global sections is supplied as input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechScalars
open FCurve Chow

variable {X : Scheme.{0}} {ι : Type} [LinearOrder ι] [Finite ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type} [CommRing R]
  (ρ : R →+* Γ(X, ⊤)) [∀ n, Module.Flat R (BaseTerm M U ρ n)]
  (hH : ∀ n, Module.Flat R (BaseHomology M U ρ (n + 1)))

include hH

/-- Flat positive cohomology makes each actual differential cokernel flat. -/
theorem baseD_cokernel_flat (n : ℕ) :
    Module.Flat R (BaseTerm M U ρ (n + 1) ⧸ (baseD M U ρ n).range) := by
  let _ := Fintype.ofFinite ι
  apply FlatCokernelStep.bounded_cokernel_flat (BaseTerm M U ρ) (baseD M U ρ)
    (baseD_comp M U ρ) _ (Fintype.card ι) (baseTerm_subsingleton M U ρ) n
  intro k
  let _ := hH k
  exact Module.Flat.of_linearEquiv (basePositiveHomologyEquiv M U ρ k).symm

/-- The cycles themselves are flat, including degree zero. -/
theorem baseD_kernel_flat (n : ℕ) : Module.Flat R (baseD M U ρ n).ker := by
  let _ := baseD_cokernel_flat M U ρ hH n
  let _ := TensorKernelFlatCokernel.range_flat (baseD M U ρ n)
  exact TensorKernelFlatCokernel.flat_kernel_of_shortExact
    (baseD M U ρ n).ker.subtype (baseD M U ρ n).rangeRestrict
    (baseD M U ρ n).ker.subtype_injective (baseD M U ρ n).surjective_rangeRestrict
    (by intro x; simp [Subtype.ext_iff])

/-- Actual global sections are flat over the original base ring. -/
theorem baseSections_flat_of_positive_flat (hCover : iSup U = ⊤) :
    Module.Flat R (baseSections M ρ ⊤) := by
  let _ := baseD_kernel_flat M U ρ hH 0
  exact Module.Flat.of_linearEquiv (baseSectionsZeroKernelEquiv M U ρ hCover)

/-- Every cycle kernel commutes with arbitrary coefficient modules. -/
theorem baseD_tensorKer_bijective (n : ℕ) (B : Type*) [AddCommGroup B] [Module R B] :
    Function.Bijective (LinearMap.tensorKer R B (baseD M U ρ n)) := by
  let _ := baseD_cokernel_flat M U ρ hH n
  exact TensorKernelFlatCokernel.tensorKer_bijective (baseD M U ρ n) B

end FLT.Mazur.IncreasingCechScalars
