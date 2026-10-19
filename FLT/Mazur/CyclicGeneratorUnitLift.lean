/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Unit relabeling of possibly colliding cyclic generators

Two generators of the same finite cyclic subgroup differ by a unit modulo
any common annihilating level. The actual order may be smaller than that
level; surjectivity on residue-class units handles this collision case.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.CyclicGeneratorUnitLift
variable {G : Type*} [Group G] {n : ℕ} [NeZero n] {x y : G}

/-- A power generating the same subgroup lifts to a unit at the full level. -/
theorem exists_unit_power (hx : x ^ n = 1) (k : ℕ)
    (hk : x ∈ Subgroup.zpowers (x ^ k)) :
    ∃ u : (ZMod n)ˣ, x ^ (u.val.val) = x ^ k := by
  have hd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hx
  have hc : k.Coprime (orderOf x) := mem_zpowers_pow_iff.mp hk
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime k hc)
  refine ⟨u, pow_eq_pow_iff_modEq.mpr ?_⟩
  have he := congrArg Units.val hu
  change ZMod.castHom hd (ZMod (orderOf x)) u.val = _ at he
  rw [← ZMod.natCast_zmod_val u.val, map_natCast, ZMod.coe_unitOfCoprime] at he
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp he

/-- Equal cyclic subgroups give a full-level unit, even when the order drops. -/
theorem exists_unit_of_zpowers_eq (hx : x ^ n = 1)
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    ∃ u : (ZMod n)ˣ, x ^ u.val.val = y := by
  have hf : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, hx⟩
  have hy : y ∈ Subgroup.zpowers x := h.symm ▸ Subgroup.mem_zpowers y
  obtain ⟨k, rfl⟩ := hf.mem_powers_iff_mem_zpowers.mpr hy
  exact exists_unit_power hx k (h ▸ Subgroup.mem_zpowers x)

end FLT.Mazur.CyclicGeneratorUnitLift
