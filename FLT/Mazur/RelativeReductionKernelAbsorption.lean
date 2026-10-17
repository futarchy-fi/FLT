/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SubmoduleQuotientScalarReduction
public import FLT.Mazur.SubmoduleReductionFlat

/-!
# Absorbing the lost boundary reduction classes by exact corrections

Flatness of the entire boundary quotient is stronger than necessary. The
relative reduction is injective exactly when every lost boundary class can
be absorbed by an original correction plus an internal scalar multiple.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RelativeSubmoduleQuotient
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (J : Ideal R) (N K : Submodule R M) (hKN : K ≤ N)

include hKN in
/-- The internal reduced denominator maps to precisely the original submodule K + JN. -/
theorem mem_relative_reduced_denominator_iff (x : N) :
    x ∈ K.comap N.subtype ⊔ J • (⊤ : Submodule R N) ↔ x.val ∈ K ⊔ J • N :=
  (relative_residue_mk_eq_zero_iff J N K x).symm.trans
    (relative_residue_mk_eq_zero_iff_mem J N K hKN x)

include hKN in
/-- Only the boundary reduction kernel modulo actual corrections must be absorbed. -/
theorem reducedInclusion_injective_iff_absorption :
    Function.Injective (reducedInclusion J N K) ↔
      N ⊓ J • (⊤ : Submodule R M) ≤ K ⊔ J • N := by
  rw [reducedInclusion_injective_iff]
  constructor
  · intro he x hx
    apply (mem_relative_reduced_denominator_iff J N K hKN ⟨x, hx.1⟩).mp
    rw [← he]
    change x ∈ K ⊔ J • (⊤ : Submodule R M)
    exact (show J • (⊤ : Submodule R M) ≤ K ⊔ J • ⊤ from le_sup_right) hx.2
  · intro habs
    apply le_antisymm _ (reduced_denominator_le J N K)
    intro x hx
    apply (mem_relative_reduced_denominator_iff J N K hKN x).mpr
    change x.val ∈ K ⊔ J • (⊤ : Submodule R M) at hx
    obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp hx
    have hzN : z ∈ N := by
      have h := N.sub_mem x.property (hKN hy)
      rw [← he, add_sub_cancel_left] at h
      exact h
    exact he ▸ (K ⊔ J • N).add_mem ((show K ≤ K ⊔ J • N from le_sup_left) hy) (habs ⟨hzN, hz⟩)

include hKN in
/-- Flatness kills the boundary reduction kernel, hence supplies the absorption condition. -/
theorem reducedInclusion_injective_of_flat_boundary [Module.Flat R (M ⧸ N)] :
    Function.Injective (reducedInclusion J N K) := by
  apply (reducedInclusion_injective_iff_absorption J N K hKN).mpr
  rw [SubmoduleReduction.inf_smul_top_of_flat_quotient]
  exact le_sup_right

include hKN in
/-- Elementwise absorption asks for one original correction, retaining the residual error in JN. -/
theorem reducedInclusion_injective_iff_corrections :
    Function.Injective (reducedInclusion J N K) ↔
      ∀ x ∈ N ⊓ J • (⊤ : Submodule R M), ∃ z ∈ K, x - z ∈ J • N := by
  rw [reducedInclusion_injective_iff_absorption J N K hKN]
  constructor
  · intro h x hx
    obtain ⟨z, hz, w, hw, he⟩ := Submodule.mem_sup.mp (h hx)
    exact ⟨z, hz, by rwa [← he, add_sub_cancel_left]⟩
  · intro h x hx
    obtain ⟨z, hz, he⟩ := h x hx
    exact Submodule.mem_sup.mpr ⟨z, hz, x - z, he, by rw [add_comm z, sub_add_cancel]⟩

end FLT.Mazur.RelativeSubmoduleQuotient
