/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SolvableNormalStep
public import Mathlib.FieldTheory.Galois.Basic

/-!
# A smaller Galois tower for the solvable induction

The fixed field of a nontrivial proper normal subgroup is Galois over the
base. Both of the resulting extension degrees are strictly smaller.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

/-- A noncyclic solvable finite Galois extension has a proper Galois tower with smaller degrees. -/
theorem solvableGalois_smaller_tower (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable Gal(L/K)]
    (hc : ¬ IsCyclic Gal(L/K)) :
    ∃ E : IntermediateField K L, IsGalois K E ∧
      Module.finrank K E < Module.finrank K L ∧
      Module.finrank E L < Module.finrank K L := by
  obtain ⟨N, hN, hbot, htop⟩ := solvable_noncyclic_normal_step Gal(L/K) hc
  let := hN
  let E := IntermediateField.fixedField N
  have hn : Module.finrank E L = Nat.card N := IntermediateField.finrank_fixedField_eq_card N
  have hright : Module.finrank E L < Module.finrank K L := by
    rw [hn, ← IsGalois.card_aut_eq_finrank]
    exact lt_of_le_of_ne N.card_le_card_group (fun h => htop (N.eq_top_of_card_eq h))
  refine ⟨E, inferInstance, ?_, hright⟩
  have hpos := Module.finrank_pos (R := K) (M := E)
  have hgt : 1 < Module.finrank E L := hn ▸ N.one_lt_card_iff_ne_bot.mpr hbot
  have hmul := Module.finrank_mul_finrank K E L
  nlinarith

end LocalClassFieldTheory
