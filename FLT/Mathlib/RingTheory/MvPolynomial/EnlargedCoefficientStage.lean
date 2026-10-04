/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.NoetherianCoefficientStage

/-! # Enlarge a specified Noetherian coefficient stage to contain further finite data -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R σ ι : Type*} [CommRing R] [Finite ι]

/-- Further finite polynomial data can be descended while retaining a given finitely
generated coefficient stage. This allows witnesses to be added after the initial presentation. -/
theorem exists_coefficient_stage_above (S : Subalgebra ℤ R) (hS : S.FG)
    (f : ι → MvPolynomial σ R) :
    ∃ T : Subalgebra ℤ R, S ≤ T ∧ T.FG ∧ IsNoetherianRing T ∧
      ∃ g : ι → MvPolynomial σ T, ∀ i, map T.val.toRingHom (g i) = f i := by
  obtain ⟨U, hU, _, g, hg⟩ := exists_noetherian_coefficient_stage f
  let T := S ⊔ U
  have hT : T.FG := hS.sup hU
  let j : U →ₐ[ℤ] T := Subalgebra.inclusion le_sup_right
  refine ⟨T, le_sup_left, hT, isNoetherianRing_of_fg hT,
    fun i ↦ map j.toRingHom (g i), fun i ↦ ?_⟩
  rw [map_map]
  exact hg i

end MvPolynomial
