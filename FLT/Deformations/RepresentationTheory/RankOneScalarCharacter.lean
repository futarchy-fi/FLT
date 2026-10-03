/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The scalar character of a rank-one group action

A commuting action on a one-dimensional vector space determines a unit
character. Its scalar-action formula is proved on every original vector.
-/

@[expose] public noncomputable section
namespace Representation

variable {F G W : Type*} [Field F] [Group G] [AddCommGroup W]
  [Module F W] [DistribMulAction G W] [SMulCommClass F G W]

/-- Every commuting rank-one action is the action of a derived unit character. -/
theorem exists_rank_one_scalar_character (hdim : Module.finrank F W = 1) :
    ∃ χ : G →* Fˣ, ∀ (g : G) (w : W), g • w = (χ g : F) • w := by
  let e : F ≃ₗ[F] W := (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some
  let c : G → F := fun g ↦ e.symm (g • e 1)
  have h (g : G) (w : W) : g • w = c g • w := by
    obtain ⟨a, rfl⟩ := e.surjective w
    have ha : e a = a • e 1 := by rw [← e.map_smul]; simp
    rw [ha, ← smul_comm a g, smul_smul, mul_comm (c g) a, ← smul_smul]
    exact congrArg (a • ·) (by simp [c, ← e.map_smul])
  have hc (g : G) : c g ≠ 0 := by
    intro hz
    have hx : e 1 ≠ 0 := fun he ↦ one_ne_zero (e.injective (he.trans e.map_zero.symm))
    have hg := h g (e 1)
    rw [hz, zero_smul] at hg
    exact hx ((smul_eq_zero_iff_eq g).mp hg)
  refine ⟨{ toFun := fun g ↦ Units.mk0 (c g) (hc g)
            map_one' := ?_
            map_mul' := ?_ }, fun g w ↦ h g w⟩
  · apply Units.ext
    simp [c]
  · intro g t
    apply Units.ext
    change c (g * t) = c g * c t
    apply e.injective
    change e (e.symm ((g * t) • e 1)) = e (c g * c t)
    rw [e.apply_symm_apply, mul_smul, h g, h t, smul_smul]
    rw [← e.map_smul]
    simp

end Representation
