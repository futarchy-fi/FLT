/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SubmoduleReductionKernel

/-!
# Split coefficient summands have no reduction kernel

An explicitly retracted inclusion commutes with ideal multiples inside its
range. This proves injective reduction for that summand over every scalar
ideal. It does not assert that an arbitrary boundary submodule is split.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SplitSubmoduleReduction
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (i : N →ₗ[R] M) (r : M →ₗ[R] N)
  (hr : r.comp i = LinearMap.id)

include hr

/-- Retraction preserves ideal divisibility of each actual included coefficient. -/
theorem preimage_smul_top (J : Ideal R) (x : N)
    (hx : i x ∈ J • (⊤ : Submodule R M)) : x ∈ J • (⊤ : Submodule R N) := by
  have h : r (i x) ∈ (J • (⊤ : Submodule R M)).map r := ⟨i x, hx, rfl⟩
  rw [Submodule.map_smul''] at h
  have he : r (i x) = x := LinearMap.congr_fun hr x
  rw [he] at h
  have hle : J • (⊤ : Submodule R M).map r ≤ J • (⊤ : Submodule R N) :=
    smul_mono_right J le_top
  exact hle h

/-- Ambient ideal multiples in the split range are exactly its internal ideal multiples. -/
theorem range_inf_smul_top (J : Ideal R) :
    LinearMap.range i ⊓ J • (⊤ : Submodule R M) = J • LinearMap.range i := by
  apply le_antisymm
  · rintro _ ⟨⟨x, rfl⟩, hx⟩
    have h := preimage_smul_top i r hr J x hx
    have hm : i x ∈ (J • (⊤ : Submodule R N)).map i := ⟨x, h, rfl⟩
    rwa [Submodule.map_smul'', Submodule.map_top] at hm
  · exact le_inf Submodule.smul_le_right (smul_mono_right J le_top)

/-- No residue class of the split range is lost in the ambient reduction. -/
theorem reduced_range_injective (J : Ideal R) :
    Function.Injective (SubmoduleReduction.inclusion J (LinearMap.range i)) :=
  (SubmoduleReduction.inclusion_injective_iff J (LinearMap.range i)).mpr
    (range_inf_smul_top i r hr J)

end FLT.Mazur.SplitSubmoduleReduction
