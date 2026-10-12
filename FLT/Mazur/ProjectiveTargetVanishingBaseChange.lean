/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTargetVanishingIdeal

/-!
# Base change of projective coefficient ideals

The coefficient ideal commutes with arbitrary scalar extension, including
nonflat extensions and localizations. The proof uses all quotient tests,
so it identifies ideals rather than only their vanishing sets.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.ProjectiveTargetVanishing
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (f : M →ₗ[R] N)
  (A C : Type*) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
  [Algebra A C] [IsScalarTower R A C]

/-- Iterated scalar extension detects exactly the same zero map as direct extension. -/
theorem iterated_baseChange_eq_zero_iff :
    (f.baseChange A).baseChange C = 0 ↔ f.baseChange C = 0 := by
  constructor
  · intro h
    ext x
    have hx := congrArg (fun g ↦
      TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C N
        (g (1 ⊗ₜ[A] (1 ⊗ₜ[R] x)))) h
    simpa using hx
  · intro h
    rw [LinearMap.baseChange_baseChange, h, LinearMap.zero_comp, LinearMap.comp_zero]

variable [Module.Projective R N]

/-- Quotients detect actual containment of coefficient ideals. -/
theorem ideal_le_iff_quotient (I : Ideal R) :
    ideal f ≤ I ↔ f.baseChange (R ⧸ I) = 0 := by
  rw [baseChange_eq_zero_iff]
  simp only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- Coefficient ideals commute with every base change, without flatness hypotheses. -/
theorem ideal_baseChange : ideal (f.baseChange A) = (ideal f).map (algebraMap R A) := by
  have h (I : Ideal A) :
      ideal (f.baseChange A) ≤ I ↔ (ideal f).map (algebraMap R A) ≤ I := by
    rw [ideal_le_iff_quotient, iterated_baseChange_eq_zero_iff,
      baseChange_eq_zero_iff, Ideal.map_le_iff_le_comap]
    rw [IsScalarTower.algebraMap_eq R A (A ⧸ I), ← RingHom.comap_ker]
    simp only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

end FLT.Mazur.ProjectiveTargetVanishing
