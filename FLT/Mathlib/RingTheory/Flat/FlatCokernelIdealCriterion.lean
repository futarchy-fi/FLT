/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.Tensor

/-! # Flat cokernels from injectivity modulo every ideal -/

@[expose] public section

open TensorProduct

namespace Module.Flat

variable {R N M Q : Type*} [CommRing R]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- A right exact sequence with flat middle term has flat cokernel if its first
map stays injective modulo every ideal. This uses the ideal tensor criterion. -/
theorem of_exact_of_lTensor_quotient_injective [Flat R M]
    (f : N →ₗ[R] M) (g : M →ₗ[R] Q) (hex : Function.Exact f g)
    (hg : Function.Surjective g)
    (hf : ∀ I : Ideal R, Function.Injective (f.lTensor (R ⧸ I))) : Flat R Q := by
  apply iff_rTensor_injective'.mpr
  intro I
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective I hg z
  have comm_g : (I.subtype.rTensor Q) ∘ₗ (g.lTensor I) =
      (g.lTensor R) ∘ₗ (I.subtype.rTensor M) := by ext; rfl
  have hym : g.lTensor R (I.subtype.rTensor M y) = 0 := by
    rw [← LinearMap.comp_apply, ← comm_g]
    change I.subtype.rTensor Q (g.lTensor I y) = 0
    rw [hy]
    exact hz
  obtain ⟨w, hw⟩ := (_root_.lTensor_exact R hex hg _).mp hym
  have comm_fπ : (I.mkQ.rTensor M) ∘ₗ (f.lTensor R) =
      (f.lTensor (R ⧸ I)) ∘ₗ (I.mkQ.rTensor N) := by ext; rfl
  have hwπ : I.mkQ.rTensor N w = 0 := by
    apply hf I
    rw [map_zero, ← LinearMap.comp_apply, ← comm_fπ]
    change I.mkQ.rTensor M (f.lTensor R w) = 0
    rw [hw]
    exact (_root_.rTensor_exact M (LinearMap.exact_subtype_mkQ I)
      I.mkQ_surjective _).mpr ⟨y, rfl⟩
  obtain ⟨v, hv⟩ := (_root_.rTensor_exact N (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective _).mp hwπ
  have comm_fι : (I.subtype.rTensor M) ∘ₗ (f.lTensor I) =
      (f.lTensor R) ∘ₗ (I.subtype.rTensor N) := by ext; rfl
  have hyv : f.lTensor I v = y := by
    apply Flat.rTensor_preserves_injective_linearMap (M := M) I.subtype Subtype.val_injective
    rw [← LinearMap.comp_apply, comm_fι]
    change f.lTensor R (I.subtype.rTensor N v) = _
    rw [hv, hw]
  have hz0 : z = 0 := by
    rw [← hy, ← hyv]
    exact (_root_.lTensor_exact I hex hg _).mpr ⟨v, rfl⟩
  exact hz0

end Module.Flat
