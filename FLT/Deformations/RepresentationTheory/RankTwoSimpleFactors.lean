/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudSimpleRepresentationQuotient
public import FLT.Deformations.RepresentationTheory.InvariantCharpoly
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Simple invariant factors of a rank-two representation

A reducible rank-two representation has an invariant line and a line quotient.
No invariant complement is required.
-/

@[expose] public noncomputable section
namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- Every one-dimensional representation is irreducible. -/
theorem isIrreducible_of_finrank_one (hV : Module.finrank k V = 1) : ρ.IsIrreducible := by
  let : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr hV
  let : Nontrivial V := IsSimpleModule.nontrivial k V
  refine { exists_pair_ne := ⟨⊥, ⊤, ρ.subrepresentation_bot_ne_top⟩
           eq_bot_or_eq_top := fun W ↦ ?_ }
  rcases eq_bot_or_eq_top W.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- Reducibility in dimension two constructs simple invariant line factors. -/
theorem exists_rank_one_factors [Module.Finite k V]
    (hV : Module.finrank k V = 2) (hρ : ¬ ρ.IsIrreducible) :
    ∃ W : Subrepresentation ρ,
      Module.finrank k W.toSubmodule = 1 ∧
      Module.finrank k (V ⧸ W.toSubmodule) = 1 ∧
      W.toRepresentation.IsIrreducible ∧
      (ρ.quotient W.toSubmodule W.apply_mem_toSubmodule).IsIrreducible := by
  have hnon : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank k V)
  have hex : ∃ W : Subrepresentation ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra! h
    exact hρ { exists_pair_ne := ⟨⊥, ⊤, ρ.subrepresentation_bot_ne_top⟩
               eq_bot_or_eq_top := fun W ↦ or_iff_not_imp_left.mpr (h W) }
  obtain ⟨W, hbot, htop⟩ := hex
  have hbot' : W.toSubmodule ≠ ⊥ := fun h ↦ hbot (Subrepresentation.toSubmodule_injective h)
  have htop' : W.toSubmodule ≠ ⊤ := fun h ↦ htop (Subrepresentation.toSubmodule_injective h)
  have hpos : 0 < Module.finrank k W.toSubmodule :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hbot')
  have hlt := Submodule.finrank_lt htop'
  have hW : Module.finrank k W.toSubmodule = 1 := by omega
  have hQ : Module.finrank k (V ⧸ W.toSubmodule) = 1 := by
    have := W.toSubmodule.finrank_quotient_add_finrank
    omega
  exact ⟨W, hW, hQ, W.toRepresentation.isIrreducible_of_finrank_one hW,
    (ρ.quotient W.toSubmodule W.apply_mem_toSubmodule).isIrreducible_of_finrank_one hQ⟩

/-- Characteristic polynomials multiply along the actual invariant line and quotient. -/
theorem charpoly_subrepresentation_mul_quotient [Module.Finite k V]
    (W : Subrepresentation ρ) (g : G) :
    (ρ g).charpoly = (W.toRepresentation g).charpoly *
      ((ρ.quotient W.toSubmodule W.apply_mem_toSubmodule) g).charpoly :=
  LinearMap.charpoly_eq_charpoly_mul_charpoly W.toSubmodule (ρ g) (W.apply_mem_toSubmodule g)

end Representation
