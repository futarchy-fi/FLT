/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Order.Atoms.Finite

/-!
# Simple quotients of finite representations

A maximal proper invariant subspace has irreducible quotient. Finite point
spaces have such a maximal proper subrepresentation whenever nonzero.
-/

@[expose] public noncomputable section
namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- A nonzero representation has distinct bottom and top subrepresentations. -/
theorem subrepresentation_bot_ne_top [Nontrivial V] :
    (⊥ : Subrepresentation ρ) ≠ ⊤ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  intro h
  exact hx (show x ∈ (⊥ : Subrepresentation ρ) from h ▸ (by trivial))

/-- The quotient by a maximal proper subrepresentation is irreducible. -/
theorem quotient_irreducible_of_isCoatom (W : Subrepresentation ρ) (hW : IsCoatom W) :
    IsIrreducible (ρ.quotient W.toSubmodule W.apply_mem_toSubmodule) := by
  let σ := ρ.quotient W.toSubmodule W.apply_mem_toSubmodule
  let : Nontrivial (V ⧸ W.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr
    (fun h ↦ hW.1 (Subrepresentation.toSubmodule_injective h))
  refine { exists_pair_ne := ⟨⊥, ⊤, subrepresentation_bot_ne_top σ⟩
           eq_bot_or_eq_top := fun U ↦ ?_ }
  let T : Subrepresentation ρ :=
    ⟨U.toSubmodule.comap W.toSubmodule.mkQ, fun g _ hx ↦ U.apply_mem_toSubmodule g hx⟩
  have hWT : W ≤ T := by
    intro x hx
    change W.toSubmodule.mkQ x ∈ U
    rw [show W.toSubmodule.mkQ x = 0 from
      (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr hx]
    exact U.toSubmodule.zero_mem
  obtain hT | hT := hW.le_iff.mp hWT
  · right
    apply top_le_iff.mp
    intro y _
    obtain ⟨x, rfl⟩ := W.toSubmodule.mkQ_surjective y
    exact (show x ∈ T from hT ▸ (by trivial))
  · left
    apply bot_unique
    intro y hy
    obtain ⟨x, rfl⟩ := W.toSubmodule.mkQ_surjective y
    change W.toSubmodule.mkQ x = 0
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr
    have hx : x ∈ T := hy
    rwa [hT] at hx

/-- A finite nonzero representation admits a maximal proper subrepresentation. -/
theorem exists_coatom_subrepresentation [Finite V] [Nontrivial V] :
    ∃ W : Subrepresentation ρ, IsCoatom W := by
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun W : Subrepresentation ρ ↦ (W : Set V)) SetLike.coe_injective
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, subrepresentation_bot_ne_top ρ⟩⟩
  exact IsCoatomic.exists_coatom (Subrepresentation ρ)

end Representation
