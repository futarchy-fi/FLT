/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterProportionality

/-!
# Rank bound for generic character functions

The augmentation and eigenvalue equations define a submodule of the actual
Galois-equivariant function algebra. The preceding proportionality theorem
bounds its rank by one.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
namespace CharacterRank

variable {F V K L : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [DistribMulAction (L ≃ₐ[K] L) V]

/-- Character functions vanishing at the identity point. -/
def functions (χ : Fˣ →* Kˣ) : Submodule K (V →[L ≃ₐ[K] L] L) where
  carrier := {f | f 0 = 0 ∧ ∀ (a : Fˣ) x,
    f ((a : F) • x) = algebraMap K L (χ a) * f x}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · change f 0 + g 0 = 0
      rw [hf.1, hg.1, add_zero]
    · intro a x
      change f ((a : F) • x) + g ((a : F) • x) = _ * (f x + g x)
      rw [hf.2, hg.2, mul_add]
  smul_mem' := by
    intro c f hf
    constructor
    · change (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K V L 0) (c • f) = 0
      rw [map_smul]
      change c • f 0 = 0
      rw [hf.1, smul_zero]
    · intro a x
      change (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K V L ((a : F) • x)) (c • f) =
        algebraMap K L (χ a) * (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K V L x) (c • f)
      rw [map_smul (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K V L ((a : F) • x)) c f,
        map_smul (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K V L x) c f]
      change c • f ((a : F) • x) = algebraMap K L (χ a) * (c • f x)
      rw [hf.2, Algebra.smul_def, Algebra.smul_def, mul_left_comm]

/-- The generic character-function module has rank at most one. -/
theorem functions_rank_le_one (hdim : Module.finrank F V = 1) (χ : Fˣ →* Kˣ) :
    Module.rank K (functions (V := V) (L := L) χ) ≤ 1 := by
  classical
  let M := functions (V := V) (L := L) χ
  apply rank_le_one_iff.mpr
  by_cases h : ∀ f : M, f = 0
  · exact ⟨0, fun g ↦ ⟨0, by simp [h g]⟩⟩
  push Not at h
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun g ↦ ?_⟩
  have hf' : (f : V →[L ≃ₐ[K] L] L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  obtain ⟨c, hc⟩ := proportional hdim χ (f : V →[L ≃ₐ[K] L] L)
    (g : V →[L ≃ₐ[K] L] L) hf' f.property.1 g.property.1
    f.property.2 g.property.2
  exact ⟨c, Subtype.ext hc.symm⟩

end CharacterRank
end ThreeAdicPlan
