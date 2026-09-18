/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.Algebra.InverseLimit.Topology
public import FLT.Deformations.DeSmitLenstra.ProfiniteFramedQuotients

/-!
# The profinite framed deformation ring

We form the inverse limit of the completed framed representation rings attached to the finite
residual quotients of a profinite group, and package it as a local proartinian algebra.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Deformation

noncomputable section

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable (n : Type) [Fintype n] [DecidableEq n]
variable [Finite (ResidueField O)]
variable (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

open ResidualQuotientIndex

/-- The inverse limit of the finite-quotient completed framed rings. -/
abbrev ProfiniteFramedLimit :=
  InverseLimit (fun U ↦ (Completion O G n rho U : Type u))
    (transitionRingHom O G n rho)

/-- The structural map from `O` to the profinite framed limit. -/
def profiniteFramedLimitAlgebraMap : O →+* ProfiniteFramedLimit O G n rho :=
  InverseLimit.liftRingHom (fun U ↦ (Completion O G n rho U : Type u))
    (transitionRingHom O G n rho)
    (fun U ↦ algebraMap O (Completion O G n rho U)) fun U V h o ↦ by
      exact (transitionMap O G n rho h).hom.commutes o

instance : Algebra O (ProfiniteFramedLimit O G n rho) :=
  (profiniteFramedLimitAlgebraMap O G n rho).toAlgebra

omit [TotallyDisconnectedSpace G] in
@[simp]
lemma algebraMap_profiniteFramedLimit_apply
    (o : O) (U : ResidualQuotientIndex O G n rho) :
    (algebraMap O (ProfiniteFramedLimit O G n rho) o).val U =
      algebraMap O (Completion O G n rho U) o :=
  rfl

/-- Projection from the profinite framed limit to a finite-quotient completion. -/
def profiniteFramedLimitComponent (U : ResidualQuotientIndex O G n rho) :
    ProfiniteFramedLimit O G n rho →+* Completion O G n rho U :=
  InverseLimit.toComponentRingHom (fun U ↦ (Completion O G n rho U : Type u))
    (transitionRingHom O G n rho) U

omit [TotallyDisconnectedSpace G] in
lemma profiniteFramedLimitComponent_continuous
    (U : ResidualQuotientIndex O G n rho) :
    Continuous (profiniteFramedLimitComponent O G n rho U) :=
  InverseLimit.toComponent_continuous
    (G := fun U ↦ (Completion O G n rho U : Type u))
    (f := transitionRingHom O G n rho) U

local instance completionCompactSpace
    (U : ResidualQuotientIndex O G n rho) : CompactSpace (Completion O G n rho U) := by
  let R := FramedCompletion O (Quotient O G n rho U) n (representation O G n rho U)
  let : TopologicalSpace R := (maximalIdeal R).adicTopology
  let : IsTopologicalRing R := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
  let : IsLocalRing.IsAdicTopology
      R := ⟨rfl⟩
  change CompactSpace R
  exact IsLocalRing.compactSpace_of_finite_residueField_of_maximalIdeal_fg
    (framedCompletion_maximalIdeal_fg O (Quotient O G n rho U) n
      (representation O G n rho U))

local instance : CompactSpace (ProfiniteFramedLimit O G n rho) :=
  InverseLimit.compactSpace fun h ↦ (transitionMap O G n rho h).hom.cont

omit [TotallyDisconnectedSpace G] in
lemma isUnit_profiniteFramedLimit_iff (x : ProfiniteFramedLimit O G n rho) :
    IsUnit x ↔ ∀ U, IsUnit (x.val U) := by
  constructor
  · intro hx U
    exact hx.map (profiniteFramedLimitComponent O G n rho U)
  · intro hx
    let y : (U : ResidualQuotientIndex O G n rho) → Completion O G n rho U :=
      fun U ↦ ↑(hx U).unit⁻¹
    have hy : ∀ U V (h : U ≤ V),
        transitionRingHom O G n rho U V h (y V) = y U := by
      intro U V h
      apply Units.eq_inv_of_mul_eq_one_left
      change x.val U * transitionRingHom O G n rho U V h (y V) = 1
      rw [← x.prop U V h, ← map_mul]
      rw [show x.val V * y V = 1 by exact (hx V).unit.mul_inv]
      exact map_one _
    refine isUnit_iff_exists.mpr ⟨⟨y, hy⟩, ?_, ?_⟩
    · ext U
      exact (hx U).unit.mul_inv
    · ext U
      exact (hx U).unit.inv_mul

local instance : Nontrivial (ProfiniteFramedLimit O G n rho) :=
  ⟨⟨0, 1, fun h ↦ by
    have h' := congrArg
      (fun x : ProfiniteFramedLimit O G n rho ↦ x.val (kernelIndex O G n rho)) h
    simp at h'⟩⟩

local instance : IsLocalRing (ProfiniteFramedLimit O G n rho) := by
  apply IsLocalRing.of_nonunits_add
  intro x y hx hy
  rw [mem_nonunits_iff] at hx hy ⊢
  rw [isUnit_profiniteFramedLimit_iff] at hx hy ⊢
  push Not at hx hy ⊢
  obtain ⟨U, hU⟩ := hx
  obtain ⟨V, hV⟩ := hy
  let W := commonRefinement O G n rho U V
  have hxW : ¬ IsUnit (x.val W) := by
    intro hxW
    exact hU (by
      simpa only [x.prop] using hxW.map (transitionRingHom O G n rho U W
        (le_commonRefinement_left O G n rho U V)))
  have hyW : ¬ IsUnit (y.val W) := by
    intro hyW
    exact hV (by
      simpa only [y.prop] using hyW.map (transitionRingHom O G n rho V W
        (le_commonRefinement_right O G n rho U V)))
  exact ⟨W, by simpa using IsLocalRing.nonunits_add hxW hyW⟩

local instance : IsLocalHom (algebraMap O (ProfiniteFramedLimit O G n rho)) := by
  constructor
  intro o ho
  have ho' := (isUnit_profiniteFramedLimit_iff O G n rho _).mp ho
    (kernelIndex O G n rho)
  change IsUnit (algebraMap O
    (Completion O G n rho (kernelIndex O G n rho)) o) at ho'
  rwa [isUnit_map_iff (algebraMap O
    (Completion O G n rho (kernelIndex O G n rho)))] at ho'

local instance : IsResidueAlgebra O (ProfiniteFramedLimit O G n rho) where
  isSurjective' := by
    intro xbar
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
    let U := kernelIndex O G n rho
    obtain ⟨o, ho⟩ := IsResidueAlgebra.algebraMap_surjective O
      (Completion O G n rho U) (IsLocalRing.residue _ (x.val U))
    refine ⟨o, ?_⟩
    change Ideal.Quotient.mk (maximalIdeal (ProfiniteFramedLimit O G n rho))
        (algebraMap O (ProfiniteFramedLimit O G n rho) o) =
      Ideal.Quotient.mk (maximalIdeal (ProfiniteFramedLimit O G n rho)) x
    rw [Ideal.Quotient.eq]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [isUnit_profiniteFramedLimit_iff]
    push Not
    refine ⟨U, ?_⟩
    change ¬ IsUnit (algebraMap O (Completion O G n rho U) o - x.val U)
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    change Ideal.Quotient.mk (maximalIdeal (Completion O G n rho U))
        (algebraMap O (Completion O G n rho U) o) =
      Ideal.Quotient.mk (maximalIdeal (Completion O G n rho U)) (x.val U) at ho
    exact Ideal.Quotient.eq.mp ho

local instance : IsProartinian (ProfiniteFramedLimit O G n rho) where
  toIsLinearTopology := inferInstance
  toT0Space := inferInstance
  toCompleteSpace := inferInstance
  isArtinianRing_quotient I hI := by
    let : Finite (ProfiniteFramedLimit O G n rho ⧸ I) :=
      AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup hI
    infer_instance

/-- The inverse limit, as a local proartinian `O`-algebra. -/
def profiniteFramedLimitObject : ProartinianCat O where
  carrier := ProfiniteFramedLimit O G n rho
  isLocalProartinianAlgebra := ⟨⟩

end

end Deformation
