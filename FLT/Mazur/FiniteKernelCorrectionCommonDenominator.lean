/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteKernelCorrectionLocalization

/-!
# A common original denominator for finitely many full corrections

Finitely many localized solutions can be cleared simultaneously. This makes
no claim that a finite family spans every boundary section; it preserves the
exact equations for the specified family only.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteKernelCorrections
variable {R : Type*} [CommRing R] (U : Submonoid R)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N)

variable {ι : Type*} [Finite ι] (x : ι → N)

/-- A product of denominators clears any specified finite family of original corrections. -/
theorem exists_common_correction
    (h : ∀ i, ∃ s : U, ∃ y : M, s.val • x i + F y = 0) :
    ∃ s : U, ∃ y : ι → M, ∀ i, s.val • x i + F (y i) = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  choose s y hy using h
  let a : U := ∏ i, s i
  let b (i : ι) : U := ∏ j ∈ Finset.univ.erase i, s j
  have hab (i : ι) : a = b i * s i := by
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  refine ⟨a, fun i ↦ (b i).val • y i, ?_⟩
  intro i
  rw [hab i, Submonoid.coe_mul, mul_smul, map_smul, ← smul_add, hy i, smul_zero]

/-- Localized solutions for a finite family yield one common original multiplier. -/
theorem localized_common_correction_iff :
    (∀ i, ∃ v, LocalizedModule.mk (x i) (1 : U) + localizedMap U F v = 0) ↔
      ∃ s : U, ∃ y : ι → M, ∀ i, s.val • x i + F (y i) = 0 := by
  constructor
  · intro h
    exact exists_common_correction U F x
      (fun i ↦ (localized_correction_iff U F (x i)).mp (h i))
  · rintro ⟨s, y, hy⟩ i
    exact (localized_correction_iff U F (x i)).mpr ⟨s, y i, hy i⟩

end FLT.Mazur.FiniteKernelCorrections
