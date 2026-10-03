/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDirectedUnion
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Data.Finset.Order

/-!
# Descending finite polynomial data to a common stage

Every polynomial over a directed union and every chosen element descend to
one stage. This supplies the finite-data step for Henselian root lifting.
-/

@[expose] public noncomputable section

open Polynomial

namespace RaynaudParameters

variable {R Ω ι : Type*} [CommRing R] [CommRing Ω]
  [Algebra R Ω] [Nonempty ι] (S : ι → Subalgebra R Ω)
  (hS : Directed (· ≤ ·) S)

include hS

/-- Every finite set of union elements is contained in one stage. -/
theorem exists_stage_finset (s : Finset (↥(⨆ i, S i))) :
    ∃ i, ∀ x ∈ s, (x : Ω) ∈ S i := by
  classical
  choose idx hidx using exists_stage_of_mem_iSup S hS
  obtain ⟨j, hj⟩ := hS.finset_le (s.image idx)
  exact ⟨j, fun x hx ↦ hj (idx x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩) (hidx x)⟩

/-- A polynomial and a proposed root descend together to one stage. -/
theorem exists_stage_polynomial (f : Polynomial (↥(⨆ i, S i)))
    (x : ↥(⨆ i, S i)) :
    ∃ i, ∃ g : Polynomial (S i), ∃ y : S i,
      g.map (Subalgebra.inclusion (le_iSup S i)).toRingHom = f ∧
      Subalgebra.inclusion (le_iSup S i) y = x := by
  classical
  obtain ⟨i, hi⟩ := exists_stage_finset S hS (insert x (f.support.image f.coeff))
  have hcoeff : ∀ n, f.coeff n ∈ Set.range (Subalgebra.inclusion (le_iSup S i)) := by
    intro n
    by_cases hn : n ∈ f.support
    · exact ⟨⟨f.coeff n, hi _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨n, hn, rfl⟩))⟩, rfl⟩
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hn]⟩
  obtain ⟨g, hg⟩ := (Polynomial.mem_lifts _).mp
    ((Polynomial.lifts_iff_coeff_lifts _).mpr hcoeff)
  exact ⟨i, g, ⟨x, hi _ (Finset.mem_insert_self _ _)⟩, hg, rfl⟩

end RaynaudParameters
