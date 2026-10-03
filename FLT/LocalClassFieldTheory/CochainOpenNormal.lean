/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CochainFiniteImage
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Open normal subgroups preserving cochain fibers

Compactness makes the set of translations preserving a discrete-valued
continuous function an open identity neighborhood. For a finite power of a
profinite group, coordinate inclusions give one subgroup in the original group.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M]

/-- All sufficiently small right translations preserve a continuous
function from a profinite group to a discrete space. -/
theorem exists_openNormal_preserving_function (c : C(G, M)) :
    ∃ N : OpenNormalSubgroup G, ∀ g ∈ N, ∀ x, c (x * g) = c x := by
  have hbad : IsClosed {p : G × G | c (p.2 * p.1) ≠ c p.2} :=
    (isClosed_discrete (s := {p : M × M | p.1 ≠ p.2})).preimage
      ((c.continuous.comp (continuous_snd.mul continuous_fst)).prodMk
        (c.continuous.comp continuous_snd))
  have hU : IsOpen {g : G | ∀ x, c (x * g) = c x} := by
    convert (isClosedMap_fst_of_compactSpace _ hbad).isOpen_compl using 1
    ext g
    simp
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hU (by simp)
  exact ⟨N, fun g hg => hN hg⟩

/-- A continuous cochain on any finite power is constant under coordinatewise
right multiplication by elements of one open normal subgroup of the original group. -/
theorem exists_openNormal_preserving_cochain {ι : Type*} [Finite ι]
    (c : C(ι → G, M)) :
    ∃ N : OpenNormalSubgroup G,
      ∀ u : ι → G, (∀ i, u i ∈ N) → ∀ x, c (x * u) = c x := by
  classical
  obtain ⟨V, hV⟩ := exists_openNormal_preserving_function c
  let U : Set G := ⋂ i : ι, (fun g : G => (Pi.mulSingle i g : ι → G)) ⁻¹' (V : Set (ι → G))
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    V.isOpen.preimage (continuous_mulSingle i)
  have h1 : (1 : G) ∈ U := by simp [U]
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  refine ⟨N, fun u hu x => hV u ?_ x⟩
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro i
  exact Set.mem_iInter.mp (hN (hu i)) i

end LocalClassFieldTheory
