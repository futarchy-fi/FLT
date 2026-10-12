/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFiberNakayama
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Lifting a finite algebra comparison from a coefficient fiber

For a finite algebra over a Noetherian local ambient ring, base flatness
and a bijective coefficient fiber force the original algebra map to be
bijective. No reducedness assumption is imposed on either ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
  [IsNoetherianRing B] [Module.Finite B A] [Module.Flat R A]

/-- Bijectivity on a coefficient quotient lifts a finite base-flat algebra map. -/
theorem finiteAlgebra_bijective_of_coefficient_fiber (J : Ideal R)
    (hJ : J.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (hf : Function.Bijective (((Algebra.linearMap B A).restrictScalars R).lTensor (R ⧸ J))) :
    Function.Bijective (algebraMap B A) := by
  let _ : Module.FinitePresentation B A := Module.finitePresentation_of_finite B A
  have hs := surjective_of_coefficient_fiber J hJ (Algebra.linearMap B A) hf.2
  exact bijective_of_coefficient_fiber J hJ (Algebra.linearMap B A) hs hf.1

/-- At a local ambient point, its coefficient residue fiber detects the whole finite map. -/
theorem finiteAlgebra_bijective_of_local_coefficient_fiber
    [IsLocalRing R] [IsLocalRing B] [IsLocalHom (algebraMap R B)]
    (hf : Function.Bijective (((Algebra.linearMap B A).restrictScalars R).lTensor
      (IsLocalRing.ResidueField R))) : Function.Bijective (algebraMap B A) :=
  finiteAlgebra_bijective_of_coefficient_fiber (IsLocalRing.maximalIdeal R)
    ((IsLocalRing.map_maximalIdeal_le (algebraMap R B)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)) hf

/-- The resulting inverse is an algebra inverse, retaining the original structural map. -/
def finiteAlgebraEquivOfLocalCoefficientFiber
    [IsLocalRing R] [IsLocalRing B] [IsLocalHom (algebraMap R B)]
    (hf : Function.Bijective (((Algebra.linearMap B A).restrictScalars R).lTensor
      (IsLocalRing.ResidueField R))) : B ≃ₐ[R] A :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R B A)
    (finiteAlgebra_bijective_of_local_coefficient_fiber hf)

/-- The constructed equivalence is the given original algebra map on every element. -/
theorem finiteAlgebraEquivOfLocalCoefficientFiber_apply
    [IsLocalRing R] [IsLocalRing B] [IsLocalHom (algebraMap R B)]
    (hf : Function.Bijective (((Algebra.linearMap B A).restrictScalars R).lTensor
      (IsLocalRing.ResidueField R))) (b : B) :
    finiteAlgebraEquivOfLocalCoefficientFiber hf b = algebraMap B A b := rfl

end FLT.Mazur.FCurve
