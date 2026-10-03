/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.KernelCocycleDescent
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous descent of a corrected two-cocycle

Once mixed terms vanish, the algebraic descent is continuous by the
quotient topology. No continuous right inverse of the quotient is used.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G H M P : Type*} [Group G] [Group H]
  [AddCommGroup M] [AddCommGroup P] [DistribMulAction G M] [DistribMulAction H P]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace M] [DiscreteTopology M]
  [TopologicalSpace P]

/-- Quotient continuity upgrades corrected cocycle descent to continuous descent. -/
theorem exists_continuous_descended_twoCocycle (f : G →* H) (hf : Function.Surjective f)
    (hq : Topology.IsQuotientMap (Prod.map f f))
    (i : P →+ M) (hi : Function.Injective i) (heq : ∀ g p, i (f g • p) = g • i p)
    (hfix : ∀ m : M, (∀ n : f.ker, (n : G) • m = m) → ∃ p, i p = m)
    (c : C(G × G, M)) (hc : IsCocycle₂ c)
    (hl : ∀ n : f.ker, ∀ g, c (n, g) = 0) (hr : ∀ g, ∀ n : f.ker, c (g, n) = 0) :
    ∃ d : C(H × H, P), IsCocycle₂ d ∧ ∀ g h, i (d (f g, f h)) = c (g, h) := by
  obtain ⟨d, hd, he⟩ := exists_descended_twoCocycle f c hc hl hr hf i hi heq hfix
  have hcomp : d ∘ Prod.map f f = Function.invFun i ∘ c := by
    funext p
    change d (f p.1, f p.2) = Function.invFun i (c (p.1, p.2))
    rw [← he]
    exact (Function.leftInverse_invFun hi _).symm
  have hcont : Continuous d := hq.continuous_iff.mpr (by
    rw [hcomp]
    exact continuous_of_discreteTopology.comp c.continuous)
  exact ⟨⟨d, hcont⟩, hd, he⟩

end LocalClassFieldTheory
