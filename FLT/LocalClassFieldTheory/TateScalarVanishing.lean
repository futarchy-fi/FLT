/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateClassArithmetic

/-!
# Vanishing of the adjacent integral scalar Tate groups

Finite groups have no nonzero characters into the integers. In degree minus
one the scalar norm is multiplication by the nonzero group order.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable (G : Type) [Group G] [Fintype G]

local notation "T" => Rep.trivial ℤ G ℤ

/-- Integral scalar Tate H¹ vanishes for every finite group. -/
theorem tateScalar_one_isZero : Limits.IsZero (tateCohomology T 1) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices h : ∀ a : tateCohomology T 1, a = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  intro a
  let e := (TateCohomology.isoGroupCohomology 1).app T ≪≫ H1IsoOfIsTrivial T
  apply e.toLinearEquiv.injective
  rw [map_zero]
  apply AddMonoidHom.ext
  intro g
  have h : Fintype.card (Additive G) • (e.hom a) g = 0 := by
    rw [← map_nsmul, card_nsmul_eq_zero, map_zero]
  change (Fintype.card (Additive G) : ℤ) * ((e.hom a) g : ℤ) = 0 at h
  have hn : (Fintype.card (Additive G) : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp h).resolve_left hn

/-- Integral scalar Tate H⁻¹ vanishes because the norm is injective. -/
theorem tateScalar_neg_one_isZero : Limits.IsZero (tateCohomology T (-1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices h : ∀ a : tateCohomology T (-1), a = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  intro a
  obtain ⟨z, hz, rfl⟩ := tateCocycleClass_surjective T (-1) a
  have hf : (Rep.norm T).hom ((chainsIso₀ T).hom z) = 0 := by
    have h := congrArg (cochainsIso₀ T).hom hz
    change (cochainsIso₀ T).hom ((cochainsIso₀ T).inv
      ((Rep.norm T).hom ((chainsIso₀ T).hom z))) = (cochainsIso₀ T).hom 0 at h
    simpa only [Iso.inv_hom_id_apply, map_zero] using h
  have hn : (Fintype.card G : ℤ) * (chainsIso₀ T).hom z = 0 := by
    simpa [Rep.norm, Representation.norm] using hf
  have he : (chainsIso₀ T).hom z = 0 :=
    (mul_eq_zero.mp hn).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  have hz0 : z = 0 := by
    apply (chainsIso₀ T).toLinearEquiv.injective
    change (chainsIso₀ T).hom z = (chainsIso₀ T).hom 0
    simpa only [map_zero] using he
  apply (tateCocycleClass_eq_zero_iff T (-1) z hz).mpr
  exact ⟨0, by rw [map_zero, hz0]⟩

end LocalClassFieldTheory
