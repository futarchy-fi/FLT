/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousTowerRefinement
public import Mathlib.Tactic.FinCases

/-!
# Fiber equations at a common tower refinement

Translate simultaneous right-translation invariance into the fiber equations
needed to descend the two-cocycle and its restricted bounding cochain.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [MulAction G M] [ContinuousSMul G M]

/-- One finite stage controls both coordinate fibers and both coefficient supports. -/
theorem exists_towerRefinement_fibers (N : Subgroup G) [CompactSpace N]
    (c : C(G × G, M)) (b : C(N, M)) (U₀ : OpenNormalSubgroup G) :
    ∃ U : OpenNormalSubgroup G, U ≤ U₀ ∧
      (∀ g h g' h', g⁻¹ * g' ∈ U → h⁻¹ * h' ∈ U → c (g, h) = c (g', h')) ∧
      (∀ g ∈ U, ∀ x, g • c x = c x) ∧
      (∀ n m : N, ((n : G)⁻¹ * m) ∈ U → b n = b m) ∧
      (∀ g ∈ U, ∀ n : N, g • b n = b n) := by
  let cf : C(Fin 2 → G, M) :=
    ⟨fun x => c (x 0, x 1), c.continuous.comp
      ((continuous_apply 0).prodMk (continuous_apply 1))⟩
  obtain ⟨U, hU, hc, hv, hb, hw⟩ := continuousTowerRefinement N cf b U₀
  refine ⟨U, hU, ?_, ?_, ?_, hw⟩
  · intro g h g' h' hg hh
    have he := hc ![g⁻¹ * g', h⁻¹ * h'] (by
      intro i
      fin_cases i
      · exact hg
      · exact hh) ![g, h]
    change c (g * (g⁻¹ * g'), h * (h⁻¹ * h')) = c (g, h) at he
    simpa only [mul_inv_cancel_left] using he.symm
  · intro g hg x
    exact hv g hg ![x.1, x.2]
  · intro n m hnm
    have he := hb (n⁻¹ * m) hnm n
    simpa only [mul_inv_cancel_left] using he.symm

end LocalClassFieldTheory
