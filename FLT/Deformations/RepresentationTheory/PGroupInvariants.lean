/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

/-!
# Normal p-subgroups on simple representations

A p-group acting linearly on a nonzero finite vector space over F_p has a
nonzero invariant vector, by counting fixed points. If the p-group is normal
in the ambient group, its invariants form a subrepresentation; irreducibility
then forces it to act trivially. This concerns simple factors, not extensions.
-/

@[expose] public section

namespace Representation

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod p) V] [Finite V]

/-- A p-group has a nonzero fixed vector on every nonzero finite F_p-module. -/
theorem exists_ne_zero_invariant_of_isPGroup [Nontrivial V]
    (ρ : Representation (ZMod p) G V) (hG : IsPGroup p G) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : G, ρ g x = x := by
  let : MulAction G V := {
    smul g x := ρ g x
    one_smul x := by change ρ 1 x = x; simp
    mul_smul g h x := by change ρ (g * h) x = ρ g (ρ h x); simp }
  have hd : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_eq_fintype_card, ZMod.card]
    exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := V)).ne'
  obtain ⟨x, hx, hx0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hd
    (show (0 : V) ∈ MulAction.fixedPoints G V from fun g ↦ (ρ g).map_zero)
  exact ⟨x, Ne.symm hx0, hx⟩

/-- Only the image of an action needs to be a p-group. -/
theorem exists_ne_zero_invariant_of_isPGroup_range [Nontrivial V]
    {H : Type*} [Group H] (ρ : Representation (ZMod p) H V) (f : G →* H)
    (hf : IsPGroup p f.range) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : G, ρ (f g) x = x := by
  obtain ⟨x, hx, hfix⟩ := exists_ne_zero_invariant_of_isPGroup
    (ρ.comp f.range.subtype) hf
  exact ⟨x, hx, fun g ↦ hfix ⟨f g, ⟨g, rfl⟩⟩⟩

omit [Finite V] in
/-- A nonzero invariant for a normal subgroup forces it to fix an irreducible module. -/
theorem normal_acts_trivially_of_exists_invariant
    (ρ : Representation (ZMod p) G V) [IsIrreducible ρ]
    (N : Subgroup G) [N.Normal]
    (h : ∃ x : V, x ≠ 0 ∧ ∀ g : N, ρ g.1 x = x) :
    ∀ g : N, ∀ x : V, ρ g.1 x = x := by
  obtain ⟨x, hx0, hx⟩ := h
  let W : Subrepresentation ρ :=
    ⟨Representation.invariants (ρ.comp N.subtype), ρ.le_comap_invariants N⟩
  have hW : W ≠ ⊥ := by
    intro h
    have hxW : x ∈ W := hx
    rw [h] at hxW
    exact hx0 hxW
  have ht : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hW
  intro g y
  have hy : y ∈ W := by rw [ht]; trivial
  exact hy g

/-- Normal p-subgroups act trivially on irreducible finite F_p-representations. -/
theorem normal_isPGroup_acts_trivially
    (ρ : Representation (ZMod p) G V) [IsIrreducible ρ]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) :
    ∀ g : N, ∀ x : V, ρ g.1 x = x := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) G) ρ.asModule
  exact normal_acts_trivially_of_exists_invariant ρ N
    (exists_ne_zero_invariant_of_isPGroup (ρ.comp N.subtype) hN)

/-- A normal subgroup with p-group automorphism image fixes every simple finite module.
This form applies to pro-p groups without asserting that their elements have finite order. -/
theorem normal_acts_trivially_of_isPGroup_image
    (ρ : Representation (ZMod p) G V) [IsIrreducible ρ]
    (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p (ρ.toHomUnits.comp N.subtype).range) :
    ∀ g : N, ∀ x : V, ρ g.1 x = x := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) G) ρ.asModule
  exact normal_acts_trivially_of_exists_invariant ρ N
    (exists_ne_zero_invariant_of_isPGroup_range
      (Units.coeHom (Module.End (ZMod p) V)) (ρ.toHomUnits.comp N.subtype) hN)

end Representation
