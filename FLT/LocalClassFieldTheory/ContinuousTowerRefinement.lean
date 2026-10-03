/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DescendedCochain

/-!
# Common refinement for a cochain and its restricted boundary

An open normal subgroup of a closed subgroup contains the trace of an
ambient open normal subgroup. Consequently one ambient finite quotient
simultaneously controls both cochains and both coefficient supports.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A subgroup identity neighborhood contains the trace of an ambient open normal subgroup. -/
theorem exists_openNormal_trace_le (N : Subgroup G) (V : OpenNormalSubgroup N) :
    ∃ U : OpenNormalSubgroup G, ∀ n : N, (n : G) ∈ U → n ∈ V := by
  obtain ⟨W, hW, he⟩ := isOpen_induced_iff.mp V.isOpen
  have h1 : (1 : G) ∈ W := by
    have h : (1 : N) ∈ Subtype.val ⁻¹' W := by rw [he]; exact V.one_mem
    exact h
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  refine ⟨U, fun n hn => ?_⟩
  change n ∈ (V.toOpenSubgroup : Set N)
  rw [← he]
  exact hU hn

variable [TopologicalSpace M] [DiscreteTopology M] [MulAction G M] [ContinuousSMul G M]

/-- Construct one refinement for ambient cochain fibers, restricted cochain fibers,
and both coefficient supports; it can refine any previously chosen stage. -/
theorem continuousTowerRefinement {ι : Type*} [Finite ι] (N : Subgroup G) [CompactSpace N]
    (c : C(ι → G, M)) (b : C(N, M)) (U₀ : OpenNormalSubgroup G) :
    ∃ U : OpenNormalSubgroup G, U ≤ U₀ ∧
      (∀ u : ι → G, (∀ i, u i ∈ U) → ∀ x, c (x * u) = c x) ∧
      (∀ g ∈ U, ∀ x, g • c x = c x) ∧
      (∀ n : N, (n : G) ∈ U → ∀ x : N, b (x * n) = b x) ∧
      (∀ g ∈ U, ∀ n : N, g • b n = b n) := by
  obtain ⟨U₁, h₁⟩ := exists_openNormal_preserving_cochain c
  obtain ⟨U₂, h₂⟩ := exists_openNormal_fixing_cochain (G := G) c
  obtain ⟨V, hV⟩ := exists_openNormal_preserving_function b
  obtain ⟨U₃, h₃⟩ := exists_openNormal_trace_le N V
  obtain ⟨U₄, h₄⟩ := exists_openNormal_fixing_cochain (G := G) b
  let U := U₀ ⊓ (U₁ ⊓ (U₂ ⊓ (U₃ ⊓ U₄)))
  refine ⟨U, inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro u hu x
    exact h₁ u (fun i => (hu i).2.1) x
  · intro g hg x
    exact h₂ g hg.2.2.1 x
  · intro n hn x
    exact hV n (h₃ n hn.2.2.2.1) x
  · intro g hg n
    exact h₄ g hg.2.2.2.2 n

end LocalClassFieldTheory
