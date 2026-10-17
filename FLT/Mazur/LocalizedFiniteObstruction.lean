/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.BaseChange

/-!
# One original denominator for finitely many localized obstructions

A specified finite family vanishes after localization precisely when one
common original denominator kills every obstruction. No Noetherian hypothesis
or finite generation of the ambient obstruction module is used.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalizedFiniteObstruction
variable {R D M ι : Type*} [CommRing R]
  [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
  (g : D →ₗ[R] M) (U : Submonoid R) (S : Type*) [CommRing S]
  [Algebra R S] [IsLocalization U S] [Finite ι] (t : ι → D)

/-- Finitely many localized zero classes have a common original annihilating denominator. -/
theorem exists_common_denominator_iff :
    (∀ j, (1 ⊗ₜ[R] g (t j) : S ⊗[R] M) = 0) ↔
      ∃ a : U, ∀ j, g (a.val • t j) = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  constructor
  · intro h
    have hj (j : ι) : ∃ a : U, g (a.val • t j) = 0 := by
      have hz := (IsLocalizedModule.eq_zero_iff U (TensorProduct.mk R S M 1)).mp (h j)
      simpa only [map_smul, Submonoid.smul_def] using hz
    choose a ha using hj
    refine ⟨∏ j, a j, fun j ↦ ?_⟩
    rw [← Finset.prod_erase_mul Finset.univ a (Finset.mem_univ j),
      Submonoid.coe_mul, mul_smul, map_smul, ha j, smul_zero]
  · rintro ⟨a, ha⟩ j
    apply (IsLocalizedModule.eq_zero_iff U (TensorProduct.mk R S M 1)).mpr
    refine ⟨a, ?_⟩
    simpa only [map_smul, Submonoid.smul_def] using ha j

end FLT.Mazur.LocalizedFiniteObstruction
