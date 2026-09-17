/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.Algebra.InverseLimit.Topology
public import FLT.Deformations.Categories
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Proartinian rings as limits of their discrete quotients

We reconstruct a local proartinian algebra from its quotients by proper open ideals.  The main
application is assembling a continuous algebra morphism from a compatible family of morphisms to
those quotients.
-/

@[expose] public section

open IsLocalRing

universe u

namespace Deformation

namespace ProartinianCat

variable {O : Type u} [CommRing O] [IsLocalRing O]

/-- Proper open ideals, ordered so that a finer quotient is a larger index. -/
abbrev OpenIdeal (S : ProartinianCat O) :=
  OrderDual { I : Ideal S // IsOpen (I : Set S) ∧ I ≠ ⊤ }

namespace OpenIdeal

variable {S : ProartinianCat O}

/-- The ideal underlying a proper open ideal. -/
def ideal (I : OpenIdeal S) : Ideal S := (OrderDual.ofDual I).1

omit [IsLocalRing O] in
lemma isOpen (I : OpenIdeal S) : IsOpen (ideal I : Set S) :=
  (OrderDual.ofDual I).2.1

omit [IsLocalRing O] in
lemma ne_top (I : OpenIdeal S) : ideal I ≠ ⊤ :=
  (OrderDual.ofDual I).2.2

omit [IsLocalRing O] in
lemma ideal_le_ideal {I J : OpenIdeal S} (h : I ≤ J) : ideal J ≤ ideal I :=
  h

/-- The maximal ideal supplies a proper open ideal. -/
noncomputable instance : Nonempty (OpenIdeal S) :=
  ⟨OrderDual.toDual ⟨maximalIdeal S, isOpen_maximalIdeal_of_isProartinian,
    (maximalIdeal.isMaximal S).ne_top⟩⟩

end OpenIdeal

variable (S : ProartinianCat O)
variable [Finite (ResidueField O)]

noncomputable instance openIdealQuotientFinite (I : OpenIdeal S) :
    Finite (S ⧸ (OpenIdeal.ideal I)) := by
  let : Nontrivial (S ⧸ (OpenIdeal.ideal I)) :=
    Ideal.Quotient.nontrivial_iff.mpr (OpenIdeal.ne_top I)
  let : IsLocalRing (S ⧸ (OpenIdeal.ideal I)) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  let : IsArtinianRing (S ⧸ (OpenIdeal.ideal I)) :=
    IsProartinian.isArtinianRing_quotient (OpenIdeal.ideal I) (OpenIdeal.isOpen I)
  let : IsLocalHom (Ideal.Quotient.mk (OpenIdeal.ideal I)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap O (S ⧸ (OpenIdeal.ideal I))) := by
    change IsLocalHom
      ((Ideal.Quotient.mk (OpenIdeal.ideal I)).comp (algebraMap O S))
    infer_instance
  let : Finite (ResidueField (S ⧸ (OpenIdeal.ideal I))) :=
    Finite.of_surjective (IsResidueAlgebra.algEquiv O (S ⧸ (OpenIdeal.ideal I)))
      (IsResidueAlgebra.algEquiv O (S ⧸ (OpenIdeal.ideal I))).surjective
  obtain ⟨m, hm⟩ :=
    IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
      (⊥ : Ideal (S ⧸ (OpenIdeal.ideal I)))
  let : Finite ((S ⧸ (OpenIdeal.ideal I)) ⧸
      (⊥ : Ideal (S ⧸ (OpenIdeal.ideal I)))) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨m, hm⟩
  exact Finite.of_surjective (RingEquiv.quotientBot (S ⧸ (OpenIdeal.ideal I)))
    (RingEquiv.quotientBot (S ⧸ (OpenIdeal.ideal I))).surjective

/-- A local proartinian algebra with finite residue field is compact. -/
noncomputable instance compactSpace : CompactSpace S := by
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace S := IsProartinian.toCompleteSpace
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, isComplete_univ⟩
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨I, hIopen, hIU⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hU
  let J : OpenIdeal S := OrderDual.toDual ⟨I ⊓ maximalIdeal S,
    hIopen.inter isOpen_maximalIdeal_of_isProartinian,
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top inf_le_right⟩
  let : Fintype (S ⧸ (OpenIdeal.ideal J)) := Fintype.ofFinite _
  let rep : (S ⧸ (OpenIdeal.ideal J)) → S := fun x ↦
    (Ideal.Quotient.mk_surjective x).choose
  refine ⟨Set.range rep, Set.finite_range rep, ?_⟩
  intro x _
  let xbar := Ideal.Quotient.mk (OpenIdeal.ideal J) x
  let y := rep xbar
  have hy : Ideal.Quotient.mk (OpenIdeal.ideal J) y = xbar :=
    (Ideal.Quotient.mk_surjective xbar).choose_spec
  refine Set.mem_iUnion_of_mem y (Set.mem_iUnion_of_mem ⟨xbar, rfl⟩ ?_)
  change x ∈ (fun z : S ↦ y + z) '' U
  refine ⟨x - y, hIU ?_, by simp⟩
  exact (show x - y ∈ OpenIdeal.ideal J from Ideal.Quotient.eq.mp hy.symm).1

/-- The transition map between quotients by proper open ideals. -/
def openIdealTransition (I J : OpenIdeal S) (h : I ≤ J) :
    (S ⧸ (OpenIdeal.ideal J)) →+* (S ⧸ (OpenIdeal.ideal I)) :=
  Ideal.Quotient.factor (OpenIdeal.ideal_le_ideal h)

instance openIdealQuotientDiscrete (I : OpenIdeal S) :
    DiscreteTopology (S ⧸ (OpenIdeal.ideal I)) :=
  QuotientAddGroup.discreteTopology (OpenIdeal.isOpen I)

/-- The inverse limit of the discrete quotients by proper open ideals. -/
abbrev OpenIdealLimit :=
  InverseLimit (fun I : OpenIdeal S ↦ S ⧸ (OpenIdeal.ideal I)) (openIdealTransition S)

/-- The canonical map to the inverse limit of the proper open-ideal quotients. -/
def toOpenIdealLimit : S →+* OpenIdealLimit S :=
  InverseLimit.liftRingHom (fun I : OpenIdeal S ↦ S ⧸ (OpenIdeal.ideal I))
    (openIdealTransition S) (fun I ↦ Ideal.Quotient.mk (OpenIdeal.ideal I))
    (fun _I _J h s ↦ Ideal.Quotient.factor_mk (OpenIdeal.ideal_le_ideal h) s)

omit [IsLocalRing O] [Finite (ResidueField O)] in
lemma toOpenIdealLimit_continuous : Continuous (toOpenIdealLimit S) :=
  InverseLimit.lift_continuous
    (fun I : OpenIdeal S ↦ Ideal.Quotient.mk (OpenIdeal.ideal I))
    (fun _I _J h s ↦ Ideal.Quotient.factor_mk (OpenIdeal.ideal_le_ideal h) s)
    (fun _ ↦ continuous_quot_mk)

omit [IsLocalRing O] [Finite (ResidueField O)] in
lemma toOpenIdealLimit_injective : Function.Injective (toOpenIdealLimit S) := by
  intro x y hxy
  by_contra h
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr h
  have hU : ({x - y}ᶜ : Set S) ∈ nhds (0 : S) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hsub.symm)
  obtain ⟨I, hIopen, hIU⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hU
  let J : OpenIdeal S := OrderDual.toDual ⟨I ⊓ maximalIdeal S,
    hIopen.inter isOpen_maximalIdeal_of_isProartinian,
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top inf_le_right⟩
  have hxyJ := congrArg (fun z : OpenIdealLimit S ↦ z.val J) hxy
  have hmem : x - y ∈ OpenIdeal.ideal J := Ideal.Quotient.eq.mp hxyJ
  have : x - y ∈ ({x - y}ᶜ : Set S) := hIU hmem.1
  exact this (by simp)

omit [IsLocalRing O] [Finite (ResidueField O)] in
lemma denseRange_toOpenIdealLimit : DenseRange (toOpenIdealLimit S) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsOpen, hsU⟩ ⟨⟨x, hx⟩, hxs⟩
  have hxs' : x ∈ s := by
    change (⟨x, hx⟩ : OpenIdealLimit S) ∈ Subtype.val ⁻¹' s
    rw [hsU]
    exact hxs
  rcases (isOpen_pi_iff.mp hsOpen) x hxs' with ⟨J, hJfinite, hJmem, hJsub⟩
  let M : Ideal S := maximalIdeal S ⊓ ⨅ j : J, OpenIdeal.ideal j.1
  have hMopen : IsOpen (M : Set S) := by
    dsimp [M]
    change IsOpen ((maximalIdeal S : Set S) ∩
      (↑(⨅ j : J, OpenIdeal.ideal j.1) : Set S))
    apply isOpen_maximalIdeal_of_isProartinian.inter
    rw [show (↑(⨅ j : J, OpenIdeal.ideal j.1) : Set S) =
      ⋂ j : J, (OpenIdeal.ideal j.1 : Set S) by ext; simp]
    exact isOpen_iInter_of_finite fun j ↦ OpenIdeal.isOpen j.1
  have hMtop : M ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top inf_le_left
  let m : OpenIdeal S := OrderDual.toDual ⟨M, hMopen, hMtop⟩
  obtain ⟨origin, horigin⟩ := Ideal.Quotient.mk_surjective (x m)
  use toOpenIdealLimit S origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsU]
  apply hJsub
  intro a ha
  let ham : a ≤ m := show OpenIdeal.ideal m ≤ OpenIdeal.ideal a from
    inf_le_right.trans (iInf_le (fun j : J ↦ OpenIdeal.ideal j.1) ⟨a, ha⟩)
  rw [← (toOpenIdealLimit S origin).prop a m ham]
  change openIdealTransition S a m ham
      (Ideal.Quotient.mk (OpenIdeal.ideal m) origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hx a m ham) (hJmem a ha).2

lemma toOpenIdealLimit_surjective : Function.Surjective (toOpenIdealLimit S) := by
  have hclosed : IsClosed (Set.range (toOpenIdealLimit S)) :=
    (toOpenIdealLimit_continuous S).isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr hclosed,
    Dense.closure_eq (denseRange_toOpenIdealLimit S)]

/-- A local proartinian algebra is the ring-theoretic inverse limit of its proper open-ideal
quotients. -/
noncomputable def openIdealLimitRingEquiv : S ≃+* OpenIdealLimit S :=
  RingEquiv.ofBijective (toOpenIdealLimit S)
    ⟨toOpenIdealLimit_injective S, toOpenIdealLimit_surjective S⟩

/-- The reconstruction equivalence is a homeomorphism. -/
noncomputable def openIdealLimitHomeomorph : S ≃ₜ OpenIdealLimit S :=
  Continuous.homeoOfEquivCompactToT2
    (f := (openIdealLimitRingEquiv S).toEquiv) (toOpenIdealLimit_continuous S)

section Lift

variable {A : Type*} [Ring A] [TopologicalSpace A]
variable (f : ∀ I : OpenIdeal S, A →+* S ⧸ (OpenIdeal.ideal I))
variable (hf : ∀ (I J : OpenIdeal S) (h : I ≤ J) (x : A),
  openIdealTransition S I J h (f J x) = f I x)

/-- A compatible family of maps to the discrete quotients, assembled as a map to their inverse
limit. -/
def compatibleLimitMap : A →+* OpenIdealLimit S :=
  InverseLimit.liftRingHom (fun I : OpenIdeal S ↦ S ⧸ (OpenIdeal.ideal I))
    (openIdealTransition S) f hf

omit [IsLocalRing O] [Finite (ResidueField O)] in
lemma compatibleLimitMap_continuous (hcont : ∀ I, Continuous (f I)) :
    Continuous (compatibleLimitMap S f hf) :=
  InverseLimit.lift_continuous f hf hcont

/-- Lift a compatible family of maps to all proper open-ideal quotients. -/
noncomputable def liftCompatibleQuotients : A →+* S :=
  (openIdealLimitRingEquiv S).symm.toRingHom.comp (compatibleLimitMap S f hf)

lemma liftCompatibleQuotients_continuous (hcont : ∀ I, Continuous (f I)) :
    Continuous (liftCompatibleQuotients S f hf) := by
  exact (openIdealLimitHomeomorph S).symm.continuous.comp
    (compatibleLimitMap_continuous S f hf hcont)

omit [TopologicalSpace A] in
@[simp]
lemma quotient_liftCompatibleQuotients (I : OpenIdeal S) :
    (Ideal.Quotient.mk (OpenIdeal.ideal I)).comp (liftCompatibleQuotients S f hf) = f I := by
  ext x
  have h := congrArg (fun z : OpenIdealLimit S ↦ z.val I)
    ((openIdealLimitRingEquiv S).apply_symm_apply (compatibleLimitMap S f hf x))
  exact h

end Lift

end ProartinianCat

end Deformation
