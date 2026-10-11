/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalScalarCohomology

/-!
# Reduction of original cohomology modulo a regular parameter

When the next cohomology vanishes, the long exact sequence identifies the
actual quotient-coefficient cohomology with reduction of original cohomology.
The comparison retains the original cohomological projection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.PrincipalScalarCohomologyReduction

open FCurve IdealPowerScalarLift

universe u

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {R : Type u} [CommRing R]
  (ρ : R →+* Γ(X, ⊤)) (M : X.Modules) (a : R)
  [Mono (scalarEnd M (ρ a))] (q : ℕ)

/-- The original cohomological reduction, with the original base action. -/
def reduction : ModuleRingH ρ M q →ₗ[R]
    ModuleRingH ρ (cokernel (scalarEnd M (ρ a))) q :=
  ((moduleRingHFunctor ρ q).map (cokernel.π (scalarEnd M (ρ a)))).hom

/-- Its kernel consists exactly of the original parameter multiples. -/
theorem reduction_ker : LinearMap.ker (reduction ρ M a q) =
    LinearMap.range (DistribSMul.toLinearMap R (ModuleRingH ρ M q) a) := by
  ext x
  exact PrincipalScalarCohomology.scalar_exact M (ρ a) q x

/-- Vanishing one degree later makes original cohomological reduction surjective. -/
theorem reduction_surjective [Subsingleton (ModuleH M (q + 1))] :
    Function.Surjective (reduction ρ M a q) :=
  PrincipalScalarCohomology.quotient_surjective M (ρ a) q

/-- Scalar reduction computes the actual quotient-coefficient cohomology. -/
def quotientEquiv [Subsingleton (ModuleH M (q + 1))] :
    (ModuleRingH ρ M q ⧸
      LinearMap.range (DistribSMul.toLinearMap R (ModuleRingH ρ M q) a)) ≃ₗ[R]
        ModuleRingH ρ (cokernel (scalarEnd M (ρ a))) q :=
  (Submodule.quotEquivOfEq _ _ (reduction_ker ρ M a q).symm).trans
    ((reduction ρ M a q).quotKerEquivOfSurjective (reduction_surjective ρ M a q))

/-- The computed quotient equivalence sends each class to its original restriction. -/
theorem quotientEquiv_mk [Subsingleton (ModuleH M (q + 1))] (x : ModuleRingH ρ M q) :
    quotientEquiv ρ M a q (Submodule.Quotient.mk x) =
      moduleHMap (cokernel.π (scalarEnd M (ρ a))) q x := by
  rw [quotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ x

end FLT.Mazur.PrincipalScalarCohomologyReduction
