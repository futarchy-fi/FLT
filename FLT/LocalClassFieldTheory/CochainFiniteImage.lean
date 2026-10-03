/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Finite coefficient support of continuous cochains

Compactness and discreteness give finite image, including after saturating
under a compact group's action. One open normal subgroup fixes every value.
This does not yet assert constancy on quotient fibers of the domain.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable {X G M : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace M] [DiscreteTopology M]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MulAction G M] [ContinuousSMul G M]

/-- A continuous cochain on a compact domain with discrete coefficients has
finite image. In particular the domain may be any finite power of a profinite group. -/
theorem cochain_range_finite (c : C(X, M)) : (Set.range c).Finite :=
  (isCompact_range c.continuous).finite_of_discrete

omit [IsTopologicalGroup G] in
/-- The action saturation of the coefficient support is still finite. -/
theorem cochain_action_range_finite (c : C(X, M)) :
    (Set.range (fun p : G × X => p.1 • c p.2)).Finite :=
  (isCompact_range (continuous_fst.smul (c.continuous.comp continuous_snd))).finite_of_discrete

variable [TotallyDisconnectedSpace G]

/-- A single open normal subgroup fixes every value of the cochain. This is
the coefficient half of finite descent; the domain fibers need a further refinement. -/
theorem exists_openNormal_fixing_cochain (c : C(X, M)) :
    ∃ N : OpenNormalSubgroup G, ∀ g ∈ N, ∀ x, g • c x = c x := by
  let U : Set G := ⋂ m ∈ Set.range c, (MulAction.stabilizer G m : Set G)
  have hU : IsOpen U := (cochain_range_finite c).isOpen_biInter fun m _ =>
    stabilizer_isOpen G m
  have h1 : (1 : G) ∈ U := by simp [U]
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  refine ⟨N, fun g hg x => ?_⟩
  have h := Set.mem_iInter₂.mp (hN hg) (c x) ⟨x, rfl⟩
  exact h

end LocalClassFieldTheory
