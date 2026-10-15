/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The additive obstruction to lifting invariant sections

A source restriction `ρ` and the difference `δ` of two relation pullbacks give
an explicit obstruction group. Changing a lift changes its difference by the
image of `ker ρ`. The resulting obstruction vanishes exactly when a correction
in that kernel makes the lift invariant. No vanishing assumption is built in.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.InvariantSectionObstruction
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (ρ : A →+ B) (δ : A →+ C)

/-- Differences obtained by changing a lift without changing its restriction. -/
def corrections : AddSubgroup C := ρ.ker.map δ

/-- The difference of a source section, modulo all permitted corrections. -/
def defect : A →+ C ⧸ corrections ρ δ :=
  (QuotientAddGroup.mk' (corrections ρ δ)).comp δ

/-- The obstruction depends only on the restricted section. -/
theorem defect_eq_of_restrict_eq {a a' : A} (h : ρ a = ρ a') :
    defect ρ δ a = defect ρ δ a' := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact ⟨a - a', by
    change ρ (a - a') = 0
    rw [map_sub, h, sub_self], map_sub δ a a'⟩

/-- Vanishing means an actual kernel correction exists. -/
theorem defect_eq_zero_iff (a : A) :
    defect ρ δ a = 0 ↔ ∃ t : A, ρ t = 0 ∧ δ t = δ a := by
  change (QuotientAddGroup.mk' (corrections ρ δ)) (δ a) = 0 ↔ _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  rfl

/-- Subtracting a kernel correction produces an invariant lift of the same section. -/
theorem defect_eq_zero_iff_invariant_lift (a : A) :
    defect ρ δ a = 0 ↔ ∃ s : A, ρ s = ρ a ∧ δ s = 0 := by
  rw [defect_eq_zero_iff]
  constructor
  · rintro ⟨t, ht, hδ⟩
    exact ⟨a - t, by rw [map_sub, ht, sub_zero], by rw [map_sub, hδ, sub_self]⟩
  · rintro ⟨s, hs, hδ⟩
    exact ⟨a - s, by rw [map_sub, hs, sub_self], by rw [map_sub, hδ, sub_zero]⟩

variable (hρ : Function.Surjective ρ)

/-- A well-defined additive obstruction on all restricted sections. -/
def obstruction : B →+ C ⧸ corrections ρ δ where
  toFun b := defect ρ δ (Classical.choose (hρ b))
  map_zero' := by
    have h := defect_eq_of_restrict_eq ρ δ
      ((Classical.choose_spec (hρ 0)).trans (map_zero ρ).symm)
    exact h.trans (map_zero (defect ρ δ))
  map_add' b b' := by
    have h : ρ (Classical.choose (hρ (b + b'))) =
        ρ (Classical.choose (hρ b) + Classical.choose (hρ b')) := by
      rw [map_add, Classical.choose_spec (hρ b), Classical.choose_spec (hρ b'),
        Classical.choose_spec (hρ (b + b'))]
    exact (defect_eq_of_restrict_eq ρ δ h).trans (map_add (defect ρ δ) _ _)

/-- Any lift computes the obstruction; the chosen preimage is immaterial. -/
theorem obstruction_restrict (a : A) :
    obstruction ρ δ hρ (ρ a) = defect ρ δ a :=
  defect_eq_of_restrict_eq ρ δ (Classical.choose_spec (hρ (ρ a)))

/-- The obstruction is zero exactly for restrictions of invariant source sections. -/
theorem obstruction_eq_zero_iff (b : B) :
    obstruction ρ δ hρ b = 0 ↔ ∃ a : A, ρ a = b ∧ δ a = 0 := by
  obtain ⟨a, rfl⟩ := hρ b
  rw [obstruction_restrict, defect_eq_zero_iff_invariant_lift]

/-- The invariant restriction has exactly the kernel of the computed obstruction as its image. -/
theorem invariant_image_eq_kernel :
    δ.ker.map ρ = (obstruction ρ δ hρ).ker := by
  ext b
  rw [AddSubgroup.mem_map, AddMonoidHom.mem_ker, obstruction_eq_zero_iff]
  exact ⟨fun ⟨a, ha, hb⟩ ↦ ⟨a, hb, ha⟩, fun ⟨a, hb, ha⟩ ↦ ⟨a, ha, hb⟩⟩

end FLT.Mazur.InvariantSectionObstruction
