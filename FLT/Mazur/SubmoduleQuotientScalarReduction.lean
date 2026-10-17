/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeSubmoduleQuotient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Scalar reduction before and after an exact submodule quotient

The residue of a quotient representative vanishes precisely in the sum of
corrections and scalar multiples. For a relative quotient those multiples
must be internal. The comparison below retains the difference as its kernel.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.RelativeSubmoduleQuotient
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (J : Ideal R) (N K : Submodule R M)

/-- Scalar multiples in a quotient pull back to corrections plus ambient multiples. -/
theorem comap_quotient_smul_top :
    (J • (⊤ : Submodule R (M ⧸ K))).comap K.mkQ = K ⊔ J • (⊤ : Submodule R M) := by
  rw [Submodule.comap_smul_top_of_surjective J K.mkQ K.mkQ_surjective,
    Submodule.ker_mkQ, sup_comm]

/-- Vanishing of a residue tensor retains both the correction and scalar ideals. -/
theorem residue_mk_eq_zero_iff (x : M) :
    (1 ⊗ₜ[R] K.mkQ x : (R ⧸ J) ⊗[R] (M ⧸ K)) = 0 ↔
      x ∈ K ⊔ J • (⊤ : Submodule R M) := by
  rw [← (quotTensorEquivQuotSMul (M ⧸ K) J).map_eq_zero_iff,
    quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  change x ∈ (J • (⊤ : Submodule R (M ⧸ K))).comap K.mkQ ↔ _
  rw [comap_quotient_smul_top]

/-- Relative residue vanishing uses internal scalar multiples of the exact boundary module. -/
theorem relative_residue_mk_eq_zero_iff (x : N) :
    (1 ⊗ₜ[R] (K.comap N.subtype).mkQ x :
      (R ⧸ J) ⊗[R] (N ⧸ K.comap N.subtype)) = 0 ↔
      x ∈ K.comap N.subtype ⊔ J • (⊤ : Submodule R N) :=
  residue_mk_eq_zero_iff J (K.comap N.subtype) x

/-- With all corrections in the boundary, the test is the original sum K + JN. -/
theorem relative_residue_mk_eq_zero_iff_mem (hKN : K ≤ N) (x : N) :
    (1 ⊗ₜ[R] (K.comap N.subtype).mkQ x :
      (R ⧸ J) ⊗[R] (N ⧸ K.comap N.subtype)) = 0 ↔ x.val ∈ K ⊔ J • N := by
  rw [relative_residue_mk_eq_zero_iff]
  have hm : (K.comap N.subtype ⊔ J • (⊤ : Submodule R N)).map N.subtype =
      K ⊔ J • N := by
    rw [Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.mpr hKN,
      Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← hm]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact N.subtype_injective he ▸ hy

/-- Internal corrections and multiples always map into their ambient counterparts. -/
theorem reduced_denominator_le :
    K.comap N.subtype ⊔ J • (⊤ : Submodule R N) ≤
      (K ⊔ J • (⊤ : Submodule R M)).comap N.subtype := by
  apply sup_le
  · exact Submodule.comap_mono le_sup_left
  · exact (Submodule.smul_top_le_comap_smul_top J N.subtype).trans
      (Submodule.comap_mono le_sup_right)

/-- The comparison of residue presentations, without asserting that it is injective. -/
def reducedInclusion :
    (N ⧸ (K.comap N.subtype ⊔ J • (⊤ : Submodule R N))) →ₗ[R]
      M ⧸ (K ⊔ J • (⊤ : Submodule R M)) :=
  (K.comap N.subtype ⊔ J • (⊤ : Submodule R N)).mapQ
    (K ⊔ J • (⊤ : Submodule R M)) N.subtype (reduced_denominator_le J N K)

/-- The reduced comparison keeps the unchanged original boundary representative. -/
theorem reducedInclusion_mk (x : N) :
    reducedInclusion J N K
      ((K.comap N.subtype ⊔ J • (⊤ : Submodule R N)).mkQ x) =
        (K ⊔ J • (⊤ : Submodule R M)).mkQ x.val := rfl

/-- The exact lost classes are ambient multiples modulo internal corrections and multiples. -/
theorem ker_reducedInclusion :
    LinearMap.ker (reducedInclusion J N K) =
      ((K ⊔ J • (⊤ : Submodule R M)).comap N.subtype).map
        (K.comap N.subtype ⊔ J • (⊤ : Submodule R N)).mkQ :=
  Submodule.ker_mapQ _ _ _ _

/-- Injectivity is exactly equality of the two original denominator submodules. -/
theorem reducedInclusion_injective_iff : Function.Injective (reducedInclusion J N K) ↔
    (K ⊔ J • (⊤ : Submodule R M)).comap N.subtype =
      K.comap N.subtype ⊔ J • (⊤ : Submodule R N) := by
  rw [← LinearMap.ker_eq_bot, ker_reducedInclusion, ← le_bot_iff,
    Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
  exact ⟨fun h ↦ le_antisymm h (reduced_denominator_le J N K), fun h ↦ h.le⟩

/-- Under the exact denominator identity, ambient residues detect relative residues. -/
theorem relative_residue_eq_zero_iff_of_injective
    (hinj : Function.Injective (reducedInclusion J N K)) (x : N) :
    (1 ⊗ₜ[R] (K.comap N.subtype).mkQ x :
      (R ⧸ J) ⊗[R] (N ⧸ K.comap N.subtype)) = 0 ↔
        (1 ⊗ₜ[R] K.mkQ x.val : (R ⧸ J) ⊗[R] (M ⧸ K)) = 0 := by
  rw [relative_residue_mk_eq_zero_iff, residue_mk_eq_zero_iff]
  change _ ↔ x ∈ (K ⊔ J • (⊤ : Submodule R M)).comap N.subtype
  rw [(reducedInclusion_injective_iff J N K).mp hinj]

end FLT.Mazur.RelativeSubmoduleQuotient
