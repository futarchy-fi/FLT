/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.StableLinePair
public import Mathlib.LinearAlgebra.Projection

/-!
# A quadratic self-twist from two permuted summands

The character records whether a group element preserves or swaps two
complementary subspaces. The intertwiner acts as +1 on the first summand
and -1 on the second. The final theorem applies when two lines exhaust the
stable lines of a normal subgroup. Exhaustion is an explicit hypothesis;
the cyclic-restriction theorem supplying it is still needed.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (H : Subgroup G)

/-- A nontrivially permuted complementary pair yields a quadratic self-twist.
The subgroup acts trivially on the pair, so the character is trivial there. -/
theorem exists_quadratic_selfTwist_of_permuted_complements
    (hchar : (2 : k) ≠ 0) {L M : Submodule k V} (hne : L ≠ M)
    (hc : IsCompl L M)
    (hperm : ∀ g : G, (L.map (ρ g) = L ∧ M.map (ρ g) = M) ∨
      (L.map (ρ g) = M ∧ M.map (ρ g) = L))
    (hmoved : ∃ g : G, L.map (ρ g) ≠ L)
    (hH : ∀ h : H, L.map (ρ (h : G)) = L) :
    ∃ χ : G →* kˣ, χ ≠ 1 ∧ (∀ h : H, χ h = 1) ∧
      (∀ g, χ g ^ 2 = 1) ∧
      ∃ e : V ≃ₗ[k] V, ∀ g, e.conj (ρ g) = (χ g : k) • ρ g := by
  classical
  let c : G → kˣ := fun g ↦ if L.map (ρ g) = L then 1 else -1
  have cmul (a b : G) : c (a * b) = c a * c b := by
    rcases hperm a with ⟨haL, haM⟩ | ⟨haL, haM⟩ <;>
      rcases hperm b with ⟨hbL, hbM⟩ | ⟨hbL, hbM⟩ <;>
      simp [c, map_mul, Module.End.mul_eq_comp, Submodule.map_comp,
        haL, haM, hbL, hne.symm]
  let χ : G →* kˣ := { toFun := c, map_one' := by simp [c, Module.End.one_eq_id], map_mul' := cmul }
  have hχ : χ ≠ 1 := by
    obtain ⟨g, hg⟩ := hmoved
    intro he
    have hv := congrArg (fun ψ : G →* kˣ ↦ (ψ g : k)) he
    have hn : (-1 : k) = 1 := by simpa [χ, c, hg] using hv
    apply hchar
    linear_combination -hn
  refine ⟨χ, hχ, ?_, ?_, ?_⟩
  · intro h
    change c h = 1
    simp [c, hH h]
  · intro g
    change c g ^ 2 = 1
    dsimp [c]
    split_ifs <;> simp
  · let f : V →ₗ[k] V := LinearMap.ofIsCompl hc L.subtype (-M.subtype)
    have fL (x : V) (hx : x ∈ L) : f x = x :=
      LinearMap.ofIsCompl_apply_left hc ⟨x, hx⟩
    have fM (x : V) (hx : x ∈ M) : f x = -x :=
      LinearMap.ofIsCompl_apply_right hc ⟨x, hx⟩
    have hf : Function.Involutive f := by
      intro v
      obtain ⟨x, y, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl hc v
      simp only [map_add, map_neg, fL x x.property, fM y y.property, neg_neg]
    let e : V ≃ₗ[k] V := LinearEquiv.ofInvolutive f hf
    have hi (g : G) (v : V) : f (ρ g v) = (c g : k) • ρ g (f v) := by
      obtain ⟨x, y, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl hc v
      have hx : ρ g x ∈ L.map (ρ g) := ⟨x, x.property, rfl⟩
      have hy : ρ g y ∈ M.map (ρ g) := ⟨y, y.property, rfl⟩
      rcases hperm g with ⟨hgL, hgM⟩ | ⟨hgL, hgM⟩
      · rw [hgL] at hx
        rw [hgM] at hy
        simp [c, hgL, map_add, fL x x.property, fM y y.property, fL _ hx, fM _ hy]
      · rw [hgL] at hx
        rw [hgM] at hy
        simp [c, hgL, hne.symm, map_add, fL x x.property, fM y y.property,
          fM _ hx, fL _ hy, add_comm]
    refine ⟨e, fun g ↦ ?_⟩
    ext v
    change f (ρ g (f v)) = (c g : k) • ρ g v
    rw [hi, hf]

/-- The two-stable-line orbit conclusion suffices to construct the twist.
The exact two-line hypothesis is separate from mere reducible restriction. -/
theorem exists_quadratic_selfTwist_of_stableLines_pair [H.Normal]
    (hchar : (2 : k) ≠ 0) {L M : Submodule k V}
    (hne : L ≠ M) (hc : IsCompl L M) (hpair : ρ.stableLines H = {L, M})
    (hmoved : ∃ g : G, L.map (ρ g) ≠ L) :
    ∃ χ : G →* kˣ, χ ≠ 1 ∧ (∀ h : H, χ h = 1) ∧
      (∀ g, χ g ^ 2 = 1) ∧
      ∃ e : V ≃ₗ[k] V, ∀ g, e.conj (ρ g) = (χ g : k) • ρ g := by
  apply ρ.exists_quadratic_selfTwist_of_permuted_complements H hchar hne hc
    (ρ.permutes_stableLine_pair H hne hpair) hmoved
  exact ρ.map_stableLine_subgroup H (by rw [hpair]; simp)

/-- Consume the exact complementary two-line orbit conclusion of W4a. -/
theorem exists_quadratic_selfTwist_of_stableLines_orbit [H.Normal]
    (hchar : (2 : k) ≠ 0)
    (horbit : ∃ L M : Submodule k V, L ≠ M ∧ IsCompl L M ∧
      ρ.stableLines H = {L, M} ∧ ∃ g : G, L.map (ρ g) = M) :
    ∃ χ : G →* kˣ, χ ≠ 1 ∧ (∀ h : H, χ h = 1) ∧
      (∀ g, χ g ^ 2 = 1) ∧
      ∃ e : V ≃ₗ[k] V, ∀ g, e.conj (ρ g) = (χ g : k) • ρ g := by
  obtain ⟨L, M, hne, hc, hpair, g, hg⟩ := horbit
  exact ρ.exists_quadratic_selfTwist_of_stableLines_pair H hchar hne hc hpair
    ⟨g, fun he ↦ hne (he.symm.trans hg)⟩

end Representation
