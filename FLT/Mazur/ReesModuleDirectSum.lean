/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.DirectSum.Module

/-!
# Direct-sum coordinates on a filtered Rees module

The polynomial model of a Rees module is linearly equivalent to the direct
sum of its actual filtration terms. The equivalence identifies every
coefficient, so it can transport geometric affine-section comparisons.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.Rees

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {I : Ideal R} (F : I.Filtration M)

/-- Assemble the actual filtration terms as polynomial coefficients. -/
def sumMap : (⨁ n : ℕ, F.N n) →ₗ[R] PolynomialModule R M :=
  DirectSum.toModule R ℕ _ (fun n ↦ (PolynomialModule.lsingle R n).comp (F.N n).subtype)

/-- A single filtration term occupies exactly its own polynomial degree. -/
lemma sumMap_of (n : ℕ) (x : F.N n) :
    sumMap F (DirectSum.lof R ℕ _ n x) = PolynomialModule.single R n x.val := by
  simp only [sumMap, DirectSum.toModule_lof, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rfl

/-- The polynomial coefficient is the original direct-sum component. -/
lemma sumMap_coeff (x : ⨁ n : ℕ, F.N n) (n : ℕ) :
    (sumMap F x).coeff n = (x n).val := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rfl
  | add x y hx hy =>
    rw [map_add, PolynomialModule.coeff_add, Finsupp.add_apply, hx, hy]
    rfl
  | of k x =>
    change (sumMap F (DirectSum.lof R ℕ _ k x)).coeff n = _
    rw [sumMap_of]
    by_cases h : k = n
    · subst n
      simp only [PolynomialModule.coeff_single, Finsupp.single_eq_same,
        DirectSum.of_eq_same]
    · simp only [PolynomialModule.coeff_single, Finsupp.single_apply,
        ite_eq_right h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      rfl

/-- Polynomial coordinates lose no direct-sum information. -/
lemma sumMap_injective : Function.Injective (sumMap F) := by
  intro x y h
  ext n
  simpa only [sumMap_coeff] using congrArg (fun p : PolynomialModule R M ↦ p.coeff n) h

/-- The polynomial coefficients are precisely the filtration submodules. -/
lemma sumMap_range : LinearMap.range (sumMap F) = F.submodule.restrictScalars R := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩ n
    rw [sumMap_coeff]
    exact (x n).property
  · intro p hp
    rw [← p.ofCoeff_coeff, ← p.coeff.sum_single, PolynomialModule.ofCoeff_finsuppSum]
    apply Submodule.sum_mem
    intro n _
    exact ⟨DirectSum.lof R ℕ _ n ⟨p.coeff n, hp n⟩, sumMap_of F n _⟩

/-- Canonical direct-sum coordinates on the complete filtered Rees module. -/
def sumEquiv : (⨁ n : ℕ, F.N n) ≃ₗ[R] F.submodule :=
  (LinearEquiv.ofInjective (sumMap F) (sumMap_injective F)).trans
    (LinearEquiv.ofEq _ _ (sumMap_range F))

/-- The equivalence retains every original coefficient. -/
lemma sumEquiv_coeff (x : ⨁ n : ℕ, F.N n) (n : ℕ) :
    (sumEquiv F x).val.coeff n = (x n).val := sumMap_coeff F x n

end FLT.Mazur.Rees
