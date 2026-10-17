/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentAlgebraHigherOrderError

/-!
# Commutation of full algebra substitutions at complementary orders

Coefficient errors of orders r and s commute when the (r+s)-th coefficient
ideal vanishes. This applies to complete algebras without a support bound.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentAlgebraHigherOrderError
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal R) (r s : ℕ) (f g : A →ₐ[R] A)
local notation "J" => Ideal.map (algebraMap R A) I

/-- The commutator error has the sum of the two coefficient orders. -/
theorem comp_sub_comp_mem
    (hf : ∀ x, f x - x ∈ J ^ r) (hg : ∀ x, g x - x ∈ J ^ s) (x : A) :
    (f.comp g) x - (g.comp f) x ∈ J ^ (r + s) := by
  have hfg := error_mem_power I r f hf s (g x - x) (hg x)
  rw [Nat.add_comm s r] at hfg
  have hgf := error_mem_power I s g hg r (f x - x) (hf x)
  convert (J ^ (r + s)).sub_mem hfg hgf using 1
  simp only [AlgHom.comp_apply, map_sub]
  ring

/-- Full substitutions commute once their mixed coefficient error vanishes. -/
theorem comp_eq_comp_of_power_eq_bot
    (hf : ∀ x, f x - x ∈ J ^ r) (hg : ∀ x, g x - x ∈ J ^ s)
    (hJ : J ^ (r + s) = ⊥) : f.comp g = g.comp f := by
  ext x
  have h := comp_sub_comp_mem I r s f g hf hg x
  rw [hJ, Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

variable (a v : A ≃ₐ[R] A)

/-- Conjugation by a full parameter depends only on its first coefficient reduction. -/
theorem conjugation_eq_of_sub_mem
    (ha : ∀ x, (a.trans v.symm) x - x ∈ J ^ r)
    (hg : ∀ x, g x - x ∈ J ^ s) (hJ : J ^ (r + s) = ⊥) :
    a.toAlgHom.comp (g.comp a.symm.toAlgHom) =
      v.toAlgHom.comp (g.comp v.symm.toAlgHom) := by
  have hc := comp_eq_comp_of_power_eq_bot I r s (a.trans v.symm).toAlgHom g ha hg hJ
  apply AlgHom.ext
  intro x
  have h := DFunLike.congr_fun hc (a.symm x)
  change v.symm (a (g (a.symm x))) = g (v.symm (a (a.symm x))) at h
  rw [AlgEquiv.apply_symm_apply] at h
  have hh := congrArg v h
  simpa only [AlgEquiv.apply_symm_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using hh

end FLT.Mazur.NilpotentAlgebraHigherOrderError
