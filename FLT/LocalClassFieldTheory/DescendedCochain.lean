/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CochainOpenNormal

/-!
# Finite quotient descent of continuous cochains

Every discrete-valued continuous cochain on a finite power of a profinite
group descends to a finite quotient, with values fixed by its open normal
kernel. No cocycle or differential comparison is assumed or asserted.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable {G M ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [Finite ι]
  [TopologicalSpace M] [DiscreteTopology M] [MulAction G M] [ContinuousSMul G M]

/-- A finite continuous quotient cochain with invariant values and its actual
inflation formula. The open normal subgroup is constructed from the cochain. -/
theorem exists_descended_cochain (c : C(ι → G, M)) :
    ∃ N : OpenNormalSubgroup G, Finite (G ⧸ N.toSubgroup) ∧
      ∃ d : C(ι → G ⧸ N.toSubgroup, M),
        (∀ x : ι → G, d (fun i => QuotientGroup.mk' N.toSubgroup (x i)) = c x) ∧
        (∀ g ∈ N, ∀ y, g • d y = d y) := by
  classical
  obtain ⟨N₁, h₁⟩ := exists_openNormal_preserving_cochain c
  obtain ⟨N₂, h₂⟩ := exists_openNormal_fixing_cochain (G := G) c
  let N := N₁ ⊓ N₂
  let q : (ι → G) → (ι → G ⧸ N.toSubgroup) :=
    fun x i => QuotientGroup.mk' N.toSubgroup (x i)
  have hq : Function.Surjective q := by
    intro y
    choose x hx using fun i => QuotientGroup.mk'_surjective N.toSubgroup (y i)
    exact ⟨x, funext hx⟩
  have hf {x y : ι → G} (h : q x = q y) : c x = c y := by
    have hi i : ∃ u ∈ N.toSubgroup, x i * u = y i :=
      (QuotientGroup.mk'_eq_mk' N.toSubgroup).mp (congrFun h i)
    choose u hu heq using hi
    have hxy : x * u = y := funext heq
    rw [← hxy, h₁ u (fun i => (hu i).1) x]
  choose r hr using hq
  let : DiscreteTopology (G ⧸ N.toSubgroup) := QuotientGroup.discreteTopology N.isOpen
  let d : C(ι → G ⧸ N.toSubgroup, M) := ⟨fun y => c (r y), continuous_of_discreteTopology⟩
  have hd (x : ι → G) : d (q x) = c x := hf (hr (q x))
  refine ⟨N, Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen, d, hd, ?_⟩
  intro g hg y
  obtain ⟨x, hx⟩ : ∃ x, q x = y := ⟨r y, hr y⟩
  rw [← hx, hd]
  exact h₂ g hg.2 x

end LocalClassFieldTheory
