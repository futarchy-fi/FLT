/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveGeneration

/-! # Finite free generation in every sufficiently large twist -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u) [Finite ι]

/-- A fixed finite free sheaf surjects onto every sufficiently large natural twist. -/
theorem exists_eventually_twist_finite_free_epi (F : (space R ι).Modules)
    [F.IsFinitePresentation] :
    ∃ (d₀ : ℕ) (κ : Type u) (_ : Finite κ), ∀ d ≥ d₀,
      ∃ (p : SheafOfModules.free κ ⟶ twistTensor R ι F (d : ℤ)), Epi p := by
  classical
  obtain ⟨m, s, _, hs⟩ := finite_chart_generators R ι F
  let κ := Σ i, Fin (m i)
  let _finiteIndex : Fintype κ := Fintype.ofFinite κ
  let t : ∀ a : κ, Γ(F, chart R ι a.1) :=
    fun a ↦ (chartSectionsIso R ι F a.1).hom (s a.1 a.2)
  choose n hn using fun a : κ ↦ sectionExtension_eventually R ι F a.1 (t a)
  refine ⟨Finset.univ.sup n, κ, inferInstance, fun d hd ↦ ?_⟩
  have hnd (a : κ) : n a ≤ d := (Finset.le_sup (Finset.mem_univ a)).trans hd
  choose σ hσ using fun a : κ ↦ hn a d (hnd a)
  refine ⟨globalEvaluation _ σ, ?_⟩
  apply globalEvaluation_epi_of_chart_generators R ι F m s d σ hs
  intro i a
  exact hσ ⟨i, a⟩

end FLT.Mazur.ProjectiveSpace
