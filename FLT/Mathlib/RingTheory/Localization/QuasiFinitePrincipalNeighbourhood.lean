/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.ZariskisMainTheorem

/-! # A principal quasi-finite neighbourhood with zero-dimensional fibres -/

@[expose] public noncomputable section

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [FiniteType R S]

/-- A quasi-finite point of a finite-type algebra has a principal neighbourhood on which
all fibres are finite-dimensional. Zariski's main theorem supplies a finite subalgebra. -/
theorem QuasiFiniteAt.exists_principal_neighbourhood (q : Ideal S) [q.IsPrime]
    [QuasiFiniteAt R q] :
    ∃ a : S, a ∉ q ∧ QuasiFinite R (Localization.Away a) := by
  obtain ⟨T, hT, a, ha, hmap⟩ :=
    QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) q
  have : Module.Finite R T := ⟨(Submodule.fg_top _).mpr hT⟩
  have : QuasiFinite R (Localization.Away a) := .trans R T _
  exact ⟨a.val, ha, .of_surjective_algHom (Localization.awayMapₐ T.val a) hmap.2⟩

/-- The principal neighbourhood has dimension at most zero on every residue fibre. -/
theorem QuasiFiniteAt.exists_principal_fibre_dimension_zero (q : Ideal S) [q.IsPrime]
    [QuasiFiniteAt R q] :
    ∃ a : S, a ∉ q ∧ ∀ (p : Ideal R) [p.IsPrime],
      ringKrullDim (p.Fiber (Localization.Away a)) ≤ 0 := by
  obtain ⟨a, ha, h⟩ := QuasiFiniteAt.exists_principal_neighbourhood (R := R) q
  have := h
  refine ⟨a, ha, fun p _ ↦ ?_⟩
  exact (Ring.krullDimLE_iff (n := 0)).mp inferInstance

end Algebra
