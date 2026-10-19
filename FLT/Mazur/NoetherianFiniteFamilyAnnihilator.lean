/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite tests for the annihilator of an arbitrary family

Choose finitely many members of the family spanning its submodule. This
requires Noetherianity only over the ambient coefficient ring, not over
any smaller ring from which a prospective annihilator may come.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NoetherianFiniteFamilyAnnihilator
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsNoetherian R M]

/-- A finite subfamily generates the same submodule, with the original indices retained. -/
theorem exists_finset_span (a : ι → M) :
    ∃ s : Finset ι, Submodule.span R (a '' (s : Set ι)) =
      Submodule.span R (Set.range a) := by
  classical
  obtain ⟨t, ht, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range a)).mp
    (IsNoetherian.noetherian (Submodule.span R (Set.range a)))
  choose idx hidx using fun x : t ↦ ht x.property
  refine ⟨Finset.univ.image idx, ?_⟩
  rw [he]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hi
    rw [hidx y]
    exact y.property
  · intro hx
    exact ⟨idx ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩,
      hidx ⟨x, hx⟩⟩

/-- The same finite subfamily tests every ambient scalar simultaneously. -/
theorem exists_finset_annihilator (a : ι → M) :
    ∃ s : Finset ι, ∀ r : R, (∀ i ∈ s, r • a i = 0) ↔ ∀ i, r • a i = 0 := by
  obtain ⟨s, hs⟩ := exists_finset_span (R := R) a
  refine ⟨s, fun r ↦ ⟨fun h i ↦ ?_, fun h i _ ↦ h i⟩⟩
  have hr : r ∈ (Submodule.span R (a '' (s : Set ι))).annihilator := by
    rw [Submodule.mem_annihilator_span]
    rintro ⟨_, j, hj, rfl⟩
    exact h j hj
  rw [hs, Submodule.mem_annihilator_span] at hr
  exact hr ⟨a i, i, rfl⟩

end FLT.Mazur.NoetherianFiniteFamilyAnnihilator
