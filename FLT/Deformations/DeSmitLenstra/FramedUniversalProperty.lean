/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.FramedCompletion
public import Mathlib.Topology.Algebra.UniformRing

/-!
# The universal property of the completed framed representation ring

For a finite group `G`, the completed framed representation ring corepresents representations
of `G` lifting a fixed residual representation. This file supplies the topological bridge from
the residual localization to its maximal-adic completion and then extends the algebraic universal
property continuously.
-/

@[expose] public section

open IsLocalRing
open CategoryTheory

universe u

namespace Deformation

noncomputable section

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [Finite G]
variable (n : Type) [Fintype n] [DecidableEq n]
variable (rho : G →* GL n (ResidueField O))

/-- The chosen commutative-ring structure on the residual localization. -/
local instance framedLocalRingCommRing : CommRing (FramedLocalRing O G n rho) :=
  inferInstance

/-- The commutative-ring structure induced on the completion. -/
local instance framedCompletionCommRing : CommRing (FramedCompletion O G n rho) :=
  inferInstance

/-- Equip the residual localization with its maximal ideal. -/
local instance framedLocalRingWithIdeal : WithIdeal (FramedLocalRing O G n rho) :=
  ⟨maximalIdeal (FramedLocalRing O G n rho)⟩

/-- Equip the completion with its maximal ideal. -/
local instance framedCompletionWithIdeal : WithIdeal (FramedCompletion O G n rho) :=
  ⟨maximalIdeal (FramedCompletion O G n rho)⟩

local instance framedLocalRing_isAdicTopology :
    IsLocalRing.IsAdicTopology (FramedLocalRing O G n rho) := ⟨rfl⟩

/-- The canonical ring homomorphism from the residual localization to its completion. -/
noncomputable def framedCompletionRingHom :
    FramedLocalRing O G n rho →+* FramedCompletion O G n rho :=
  algebraMap (FramedLocalRing O G n rho) (FramedCompletion O G n rho)

lemma framedCompletionRingHom_isLocalHom :
    IsLocalHom (framedCompletionRingHom O G n rho) := by
  change IsLocalHom
    (algebraMap (FramedLocalRing O G n rho) (FramedCompletion O G n rho))
  infer_instance

lemma framedCompletion_sub_mem_maximalIdeal_pow_iff
    (a b : FramedLocalRing O G n rho) (m : ℕ) :
    framedCompletionRingHom O G n rho a - framedCompletionRingHom O G n rho b ∈
        maximalIdeal (FramedCompletion O G n rho) ^ m ↔
      a - b ∈ maximalIdeal (FramedLocalRing O G n rho) ^ m := by
  change AdicCompletion.of (maximalIdeal (FramedLocalRing O G n rho))
      (FramedLocalRing O G n rho) a -
    AdicCompletion.of (maximalIdeal (FramedLocalRing O G n rho))
      (FramedLocalRing O G n rho) b ∈ _ ↔ _
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  rw [← Submodule.restrictScalars_mem (FramedLocalRing O G n rho),
    ← Ideal.smul_top_eq_map]
  rw [AdicCompletion.pow_smul_top_eq_ker_eval
    (maximalIdeal (FramedLocalRing O G n rho)).fg_of_isNoetherianRing]
  simp only [LinearMap.mem_ker, AdicCompletion.eval, LinearMap.coe_mk, AddHom.coe_mk,
    AdicCompletion.of_apply, Submodule.mkQ_apply, map_sub]
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  simp

/-- The canonical map to the completion induces the original maximal-adic uniformity. -/
lemma framedCompletionRingHom_isUniformInducing :
    IsUniformInducing (framedCompletionRingHom O G n rho) := by
  apply AddMonoidHom.isUniformInducing_of_isInducing
  apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
  let hL := Ideal.hasBasis_nhds_zero_adic
    (maximalIdeal (FramedLocalRing O G n rho))
  let hC := (Ideal.hasBasis_nhds_zero_adic
    (maximalIdeal (FramedCompletion O G n rho))).comap
      (framedCompletionRingHom O G n rho)
  apply hL.ext hC
  · intro m _
    refine ⟨m, trivial, fun a ha ↦ ?_⟩
    change framedCompletionRingHom O G n rho a ∈
      maximalIdeal (FramedCompletion O G n rho) ^ m at ha
    have h := (framedCompletion_sub_mem_maximalIdeal_pow_iff O G n rho a 0 m).mp
      (by simpa only [map_zero, sub_zero] using ha)
    change a ∈ maximalIdeal (FramedLocalRing O G n rho) ^ m
    simpa only [sub_zero] using h
  · intro m _
    refine ⟨m, trivial, fun a ha ↦ ?_⟩
    change a ∈ maximalIdeal (FramedLocalRing O G n rho) ^ m at ha
    have h := (framedCompletion_sub_mem_maximalIdeal_pow_iff O G n rho a 0 m).mpr
      (by simpa only [sub_zero] using ha)
    change framedCompletionRingHom O G n rho a ∈
      maximalIdeal (FramedCompletion O G n rho) ^ m
    simpa only [map_zero, sub_zero] using h

/-- The residual localization has dense image in its maximal-adic completion. -/
lemma framedCompletionRingHom_denseRange :
    DenseRange (framedCompletionRingHom O G n rho) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨m, -, hm⟩ :=
    (Ideal.hasBasis_nhds_adic (maximalIdeal (FramedCompletion O G n rho)) x).mem_iff.mp
      (hU.mem_nhds hx)
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (p := maximalIdeal (FramedLocalRing O G n rho) ^ m • ⊤) (x.1 m)
  have hax : framedCompletionRingHom O G n rho a - x ∈
      maximalIdeal (FramedCompletion O G n rho) ^ m := by
    change AdicCompletion.of (maximalIdeal (FramedLocalRing O G n rho))
      (FramedLocalRing O G n rho) a - x ∈ _
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem (FramedLocalRing O G n rho),
      ← Ideal.smul_top_eq_map]
    rw [AdicCompletion.pow_smul_top_eq_ker_eval
      (maximalIdeal (FramedLocalRing O G n rho)).fg_of_isNoetherianRing]
    change AdicCompletion.eval (maximalIdeal (FramedLocalRing O G n rho))
      (FramedLocalRing O G n rho) m
        (AdicCompletion.of (maximalIdeal (FramedLocalRing O G n rho))
          (FramedLocalRing O G n rho) a - x) = 0
    rw [map_sub, AdicCompletion.eval_of, sub_eq_zero, AdicCompletion.eval_apply]
    exact ha
  refine ⟨framedCompletionRingHom O G n rho a, hm ?_, Set.mem_range_self a⟩
  refine ⟨framedCompletionRingHom O G n rho a - x, hax, ?_⟩
  abel_nf

omit [IsNoetherianRing O] [Finite G] in
/-- The framed coordinate algebra is dense in its localization at the residual ideal. -/
lemma framedRepresentationToLocalRing_denseRange : DenseRange
    (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n rho)) := by
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨m, -, hm⟩ :=
    (Ideal.hasBasis_nhds_adic (maximalIdeal (FramedLocalRing O G n rho)) x).mem_iff.mp
      (hU.mem_nhds hx)
  let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow
    (residualRepresentationIdeal O G n rho) (FramedLocalRing O G n rho) m
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (e.symm (Ideal.Quotient.mk (maximalIdeal (FramedLocalRing O G n rho) ^ m) x))
  have hax : algebraMap (FramedRepresentationRing O G n)
      (FramedLocalRing O G n rho) a - x ∈
      maximalIdeal (FramedLocalRing O G n rho) ^ m := by
    rw [← Ideal.Quotient.eq]
    change e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ x
    rw [ha, e.apply_symm_apply]
  refine ⟨algebraMap (FramedRepresentationRing O G n)
      (FramedLocalRing O G n rho) a, hm ?_, Set.mem_range_self a⟩
  refine ⟨algebraMap (FramedRepresentationRing O G n)
      (FramedLocalRing O G n rho) a - x, hax, ?_⟩
  abel_nf

section UniversalProperty

variable [Finite (ResidueField O)]

/-- The dense localization map, with codomain viewed as the bundled completion. -/
noncomputable def framedCompletionRingHomObject :
    FramedLocalRing O G n rho →+* framedCompletionObject O G n rho where
  toFun := framedCompletionRingHom O G n rho
  map_one' := map_one (framedCompletionRingHom O G n rho)
  map_mul' := map_mul (framedCompletionRingHom O G n rho)
  map_zero' := map_zero (framedCompletionRingHom O G n rho)
  map_add' := map_add (framedCompletionRingHom O G n rho)

lemma framedCompletionRingHomObject_denseRange :
    DenseRange (framedCompletionRingHomObject O G n rho) :=
  framedCompletionRingHom_denseRange O G n rho

/-- The structural map from the framed coordinate algebra to its residual completion. -/
noncomputable def framedRepresentationToCompletion :
    FramedRepresentationRing O G n →ₐ[O] FramedCompletion O G n rho :=
  (IsScalarTower.toAlgHom O (FramedLocalRing O G n rho)
      (FramedCompletion O G n rho)).comp
    (IsScalarTower.toAlgHom O (FramedRepresentationRing O G n)
      (FramedLocalRing O G n rho))

/-- The structural map, with its codomain viewed as the bundled proartinian object. -/
noncomputable def framedRepresentationToCompletionObject :
    FramedRepresentationRing O G n →ₐ[O] framedCompletionObject O G n rho where
  toFun := framedRepresentationToCompletion O G n rho
  map_one' := map_one (framedRepresentationToCompletion O G n rho)
  map_mul' := map_mul (framedRepresentationToCompletion O G n rho)
  map_zero' := map_zero (framedRepresentationToCompletion O G n rho)
  map_add' := map_add (framedRepresentationToCompletion O G n rho)
  commutes' := (framedRepresentationToCompletion O G n rho).commutes

omit [Finite (ResidueField O)] in
/-- The framed coordinate algebra is dense in its residual completion. -/
lemma framedRepresentationToCompletion_denseRange : DenseRange
    (framedRepresentationToCompletion O G n rho) :=
  (framedCompletionRingHom_denseRange O G n rho).comp
    (framedRepresentationToLocalRing_denseRange O G n rho)
    (framedCompletionRingHom_isUniformInducing O G n rho).uniformContinuous.continuous

/-- The coordinate map into the bundled residual completion has dense range. -/
lemma framedRepresentationToCompletionObject_denseRange : DenseRange
    (framedRepresentationToCompletionObject O G n rho) :=
  framedRepresentationToCompletion_denseRange O G n rho

omit [Finite (ResidueField O)] in
lemma framedRepresentationToCompletion_comap_maximalIdeal :
    (maximalIdeal (FramedCompletion O G n rho)).comap
        (framedRepresentationToCompletion O G n rho).toRingHom =
      residualRepresentationIdeal O G n rho := by
  let : IsLocalHom (framedCompletionRingHom O G n rho) :=
    framedCompletionRingHom_isLocalHom O G n rho
  change (maximalIdeal (FramedCompletion O G n rho)).comap
      ((framedCompletionRingHom O G n rho).comp
        (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n rho))) = _
  rw [← Ideal.comap_comap,
    IsLocalRing.maximalIdeal_comap (framedCompletionRingHom O G n rho)]
  exact IsLocalization.AtPrime.under_maximalIdeal
    (FramedLocalRing O G n rho) (residualRepresentationIdeal O G n rho)

lemma framedRepresentationToCompletionObject_comap_maximalIdeal :
    (maximalIdeal (framedCompletionObject O G n rho)).comap
        (framedRepresentationToCompletionObject O G n rho).toRingHom =
      residualRepresentationIdeal O G n rho := by
  change (maximalIdeal (FramedCompletion O G n rho)).comap
      (framedRepresentationToCompletion O G n rho).toRingHom = _
  exact framedRepresentationToCompletion_comap_maximalIdeal O G n rho

lemma framedCompletion_toResidue_apply (a : FramedRepresentationRing O G n) :
    (ProartinianCat.toResidueField (framedCompletionObject O G n rho)).hom
        (framedRepresentationToCompletion O G n rho a) =
      residualRepresentationHom O G n rho a := by
  let q := (ProartinianCat.toResidueField
    (framedCompletionObject O G n rho)).hom
  let f := framedRepresentationToCompletionObject O G n rho
  obtain ⟨o, ho⟩ := residue_surjective (residualRepresentationHom O G n rho a)
  have hp : a - algebraMap O (FramedRepresentationRing O G n) o ∈
      residualRepresentationIdeal O G n rho := by
    change residualRepresentationHom O G n rho
      (a - algebraMap O (FramedRepresentationRing O G n) o) = 0
    rw [map_sub, sub_eq_zero, (residualRepresentationHom O G n rho).commutes o]
    exact ho.symm
  have hzero : q (f (a - algebraMap O (FramedRepresentationRing O G n) o)) = 0 := by
    change f (a - algebraMap O (FramedRepresentationRing O G n) o) ∈ RingHom.ker q
    rw [ProartinianCat.ker_toResidueField]
    exact (show a - algebraMap O (FramedRepresentationRing O G n) o ∈
      (maximalIdeal (framedCompletionObject O G n rho)).comap f.toRingHom from
        (framedRepresentationToCompletionObject_comap_maximalIdeal O G n rho).symm ▸ hp)
  have hfirst : q (f a) = q (f (algebraMap O (FramedRepresentationRing O G n) o)) := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact hzero
  have hscalar : q (f (algebraMap O (FramedRepresentationRing O G n) o)) =
      algebraMap O (ResidueField O) o := by
    change (ProartinianCat.toResidueField (framedCompletionObject O G n rho)).hom
      (algebraMap O (framedCompletionObject O G n rho) o) =
        algebraMap O (ProartinianCat.residueField (𝓞 := O)) o
    exact (ProartinianCat.toResidueField (framedCompletionObject O G n rho)).hom.commutes o
  exact hfirst.trans (hscalar.trans ho)

/-- A framed lift of `rho` to `S` is a representation whose canonical residue is `rho`. -/
def IsFramedLift (S : ProartinianCat O) (tau : G →* GL n S) : Prop :=
  (Matrix.GeneralLinearGroup.map (ProartinianCat.toResidueField S).hom.toRingHom).comp tau = rho

/-- Framed lifts of `rho` to a local proartinian algebra. -/
def FramedLifts (S : ProartinianCat O) :=
  { tau : G →* GL n S // IsFramedLift O G n rho S tau }

omit [IsNoetherianRing O] [Finite G] [Finite (ResidueField O)] in
lemma residualRepresentationHom_eq_comp_of_isFramedLift
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    (ProartinianCat.toResidueField S).hom.toAlgHom.comp
        (FramedRepresentationRing.ofRepresentation tau) =
      residualRepresentationHom O G n rho := by
  have hcomp :
      (ProartinianCat.toResidueField S).hom.toAlgHom.comp
          (FramedRepresentationRing.ofRepresentation tau) =
        FramedRepresentationRing.ofRepresentation
          ((Matrix.GeneralLinearGroup.map
            (ProartinianCat.toResidueField S).hom.toRingHom).comp tau) := by
    apply RingQuot.ringQuot_ext'
    apply MvPolynomial.algHom_ext
    rintro ⟨g, i, j⟩
    simp [FramedRepresentationRing.ofRepresentation]
  rw [hcomp, h]
  rfl

/-- A framed lift induces an algebra map out of the localization at the residual ideal. -/
noncomputable def framedLocalRingMap
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    FramedLocalRing O G n rho →ₐ[O] S :=
  IsLocalization.liftAlgHom (M := (residualRepresentationIdeal O G n rho).primeCompl)
    (f := FramedRepresentationRing.ofRepresentation tau) fun y ↦ by
      apply notMem_maximalIdeal.mp
      intro hy
      have hz : (ProartinianCat.toResidueField S).hom
          (FramedRepresentationRing.ofRepresentation tau y.1) = 0 := by
        change FramedRepresentationRing.ofRepresentation tau y.1 ∈
          RingHom.ker (ProartinianCat.toResidueField S).hom
        rwa [ProartinianCat.ker_toResidueField]
      apply y.2
      change residualRepresentationHom O G n rho y.1 = 0
      rw [← residualRepresentationHom_eq_comp_of_isFramedLift O G n rho S tau h]
      exact hz

omit [IsNoetherianRing O] [Finite G] [Finite (ResidueField O)] in
lemma framedLocalRingMap_isLocalHom
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    IsLocalHom (framedLocalRingMap O G n rho S tau h).toRingHom := by
  let f := (framedLocalRingMap O G n rho S tau h).toRingHom
  let q := (ProartinianCat.toResidueField S).hom.toRingHom
  have hsurj : Function.Surjective (q.comp f) := by
    intro x
    obtain ⟨o, rfl⟩ := residue_surjective x
    refine ⟨algebraMap O (FramedLocalRing O G n rho) o, ?_⟩
    change (ProartinianCat.toResidueField S).hom
      (framedLocalRingMap O G n rho S tau h
        (algebraMap O (FramedLocalRing O G n rho) o)) =
      algebraMap O (ResidueField O) o
    rw [(framedLocalRingMap O G n rho S tau h).commutes o]
    exact (ProartinianCat.toResidueField S).hom.commutes o
  apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
  rw [← ProartinianCat.ker_toResidueField S]
  change (RingHom.ker q).comap f = maximalIdeal (FramedLocalRing O G n rho)
  rw [RingHom.comap_ker]
  change RingHom.ker (q.comp f) = maximalIdeal (FramedLocalRing O G n rho)
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)

omit [IsNoetherianRing O] [Finite G] [Finite (ResidueField O)] in
lemma framedLocalRingMap_continuous
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    Continuous (framedLocalRingMap O G n rho S tau h) := by
  let : IsLocalHom (framedLocalRingMap O G n rho S tau h).toRingHom :=
    framedLocalRingMap_isLocalHom O G n rho S tau h
  exact isContinuous_of_isProartinian_of_isLocalHom
    (framedLocalRingMap O G n rho S tau h).toRingHom

omit [IsNoetherianRing O] [Finite G] [Finite (ResidueField O)] in
lemma framedLocalRingMap_uniformContinuous
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    letI := IsTopologicalAddGroup.rightUniformSpace S
    UniformContinuous (framedLocalRingMap O G n rho S tau h) := by
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  exact uniformContinuous_addMonoidHom_of_continuous
    (framedLocalRingMap_continuous O G n rho S tau h)

/-- The continuous algebra map from the completed framed ring induced by a framed lift. -/
noncomputable def framedCompletionMap
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    FramedCompletion O G n rho →A[O] S := by
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace S := IsProartinian.toCompleteSpace
  let : T2Space S := inferInstance
  let i := framedCompletionRingHom O G n rho
  let ui := framedCompletionRingHom_isUniformInducing O G n rho
  let dr := framedCompletionRingHom_denseRange O G n rho
  let f := (framedLocalRingMap O G n rho S tau h).toRingHom
  let hf : UniformContinuous f := framedLocalRingMap_uniformContinuous O G n rho S tau h
  let di := ui.isDenseInducing dr
  let F := IsDenseInducing.extendRingHom ui dr hf
  exact
    { toAlgHom :=
        { __ := F
          commutes' := fun o ↦ by
            change di.extend f (algebraMap O (FramedCompletion O G n rho) o) =
              algebraMap O S o
            rw [IsScalarTower.algebraMap_apply O (FramedLocalRing O G n rho)
              (FramedCompletion O G n rho)]
            change di.extend f (i (algebraMap O (FramedLocalRing O G n rho) o)) = _
            rw [di.extend_eq hf.continuous]
            exact (framedLocalRingMap O G n rho S tau h).commutes o }
      cont := (uniformContinuous_uniformly_extend ui dr hf).continuous }

/-- The completion map, with its domain viewed as the bundled proartinian object. -/
noncomputable def framedCompletionMapObject
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    framedCompletionObject O G n rho →A[O] S where
  toFun := framedCompletionMap O G n rho S tau h
  map_one' := map_one (framedCompletionMap O G n rho S tau h)
  map_mul' := map_mul (framedCompletionMap O G n rho S tau h)
  map_zero' := map_zero (framedCompletionMap O G n rho S tau h)
  map_add' := map_add (framedCompletionMap O G n rho S tau h)
  commutes' := (framedCompletionMap O G n rho S tau h).commutes
  cont := (framedCompletionMap O G n rho S tau h).cont

omit [IsNoetherianRing O] [Finite G] [Finite (ResidueField O)] in
@[simp]
lemma framedLocalRingMap_algebraMap
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau)
    (a : FramedRepresentationRing O G n) :
    framedLocalRingMap O G n rho S tau h
        (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n rho) a) =
      FramedRepresentationRing.ofRepresentation tau a := by
  exact IsLocalization.lift_eq _ a

omit [Finite (ResidueField O)] in
@[simp]
lemma framedCompletionMap_framedCompletionRingHom
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau)
    (a : FramedLocalRing O G n rho) :
    framedCompletionMap O G n rho S tau h (framedCompletionRingHom O G n rho a) =
      framedLocalRingMap O G n rho S tau h a := by
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace S := IsProartinian.toCompleteSpace
  let : T2Space S := inferInstance
  let i := framedCompletionRingHom O G n rho
  let ui := framedCompletionRingHom_isUniformInducing O G n rho
  let dr := framedCompletionRingHom_denseRange O G n rho
  let f := (framedLocalRingMap O G n rho S tau h).toRingHom
  let hf : UniformContinuous f := framedLocalRingMap_uniformContinuous O G n rho S tau h
  let di := ui.isDenseInducing dr
  change di.extend f (i a) = f a
  exact di.extend_eq hf.continuous a

omit [Finite (ResidueField O)] in
lemma framedCompletionMap_universalFramedLift
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau) :
    (Matrix.GeneralLinearGroup.map
      (framedCompletionMap O G n rho S tau h).toRingHom).comp
        (universalFramedLift O G n rho) = tau := by
  ext g i j
  change framedCompletionMap O G n rho S tau h
      (framedCompletionRingHom O G n rho
        (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n rho)
          (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j)))))) =
    tau g i j
  rw [framedCompletionMap_framedCompletionRingHom, framedLocalRingMap_algebraMap]
  simp [FramedRepresentationRing.ofRepresentation, framedRepresentationQuotient]

lemma universalFramedLift_isFramedLift :
    IsFramedLift O G n rho (framedCompletionObject O G n rho)
      (universalFramedLift O G n rho) := by
  ext g i j
  change (ProartinianCat.toResidueField (framedCompletionObject O G n rho)).hom
      (framedRepresentationToCompletion O G n rho
        (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j))))) =
    rho g i j
  rw [framedCompletion_toResidue_apply]
  simp [residualRepresentationHom, FramedRepresentationRing.ofRepresentation,
    framedRepresentationQuotient]
  rfl

/-- A map from the universal completion sends its universal lift to a framed lift. -/
noncomputable def framedCompletionHomToLift
    (S : ProartinianCat O) (f : framedCompletionObject O G n rho ⟶ S) :
    FramedLifts O G n rho S := by
  refine ⟨(Matrix.GeneralLinearGroup.map f.hom.toRingHom).comp
    (universalFramedLift O G n rho), ?_⟩
  have hres : f ≫ ProartinianCat.toResidueField S =
      ProartinianCat.toResidueField (framedCompletionObject O G n rho) :=
    Subsingleton.elim _ _
  ext g i j
  change (f ≫ ProartinianCat.toResidueField S).hom
      (framedRepresentationToCompletionObject O G n rho
        (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j))))) = rho g i j
  rw [hres]
  exact framedCompletion_toResidue_apply O G n rho _ |>.trans (by
    simp [residualRepresentationHom, FramedRepresentationRing.ofRepresentation,
      framedRepresentationQuotient]
    rfl)

/-- A framed lift determines a morphism from the universal completion. -/
noncomputable def framedCompletionLiftToHom
    (S : ProartinianCat O) (tau : FramedLifts O G n rho S) :
    framedCompletionObject O G n rho ⟶ S :=
  ⟨framedCompletionMapObject O G n rho S tau.1 tau.2⟩

lemma framedCompletionHom_unique
    (S : ProartinianCat O) (tau : G →* GL n S) (h : IsFramedLift O G n rho S tau)
    (f : framedCompletionObject O G n rho ⟶ S)
    (hf : (Matrix.GeneralLinearGroup.map f.hom.toRingHom).comp
      (universalFramedLift O G n rho) = tau) :
    f = framedCompletionLiftToHom O G n rho S ⟨tau, h⟩ := by
  have hA : f.hom.toAlgHom.comp (framedRepresentationToCompletionObject O G n rho) =
      FramedRepresentationRing.ofRepresentation tau := by
    apply RingQuot.ringQuot_ext'
    apply MvPolynomial.algHom_ext
    rintro ⟨g, i, j⟩
    have hg := congrArg
      (fun r : G →* GL n S ↦ ((r g : GL n S) : Matrix n n S) i j) hf
    change f.hom
      (framedRepresentationToCompletionObject O G n rho
        (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j))))) =
      tau g i j at hg
    change f.hom
      (framedRepresentationToCompletionObject O G n rho
        (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j))))) =
      FramedRepresentationRing.ofRepresentation tau
        (framedRepresentationQuotient O G n (MvPolynomial.X (g, (i, j))))
    simpa [FramedRepresentationRing.ofRepresentation, framedRepresentationQuotient] using hg
  have hL : f.hom.toRingHom.comp (framedCompletionRingHomObject O G n rho) =
      (framedLocalRingMap O G n rho S tau h).toRingHom := by
    apply IsLocalization.ringHom_ext
      (residualRepresentationIdeal O G n rho).primeCompl
    apply RingHom.ext
    intro a
    change f.hom
      (framedRepresentationToCompletionObject O G n rho a) =
      framedLocalRingMap O G n rho S tau h
        (algebraMap (FramedRepresentationRing O G n)
          (FramedLocalRing O G n rho) a)
    rw [framedLocalRingMap_algebraMap]
    exact DFunLike.congr_fun hA a
  apply ProartinianCat.hom_ext
  apply DFunLike.ext _ _
  intro x
  apply congr_fun (framedCompletionRingHomObject_denseRange O G n rho |>.equalizer
    f.hom.cont
    (framedCompletionLiftToHom O G n rho S ⟨tau, h⟩).hom.cont ?_) x
  funext a
  change f.hom (framedCompletionRingHomObject O G n rho a) =
    framedCompletionMapObject O G n rho S tau h
      (framedCompletionRingHomObject O G n rho a)
  rw [show f.hom (framedCompletionRingHomObject O G n rho a) =
    framedLocalRingMap O G n rho S tau h a from DFunLike.congr_fun hL a]
  exact (framedCompletionMap_framedCompletionRingHom O G n rho S tau h a).symm

@[simp]
lemma framedCompletionHomToLift_liftToHom
    (S : ProartinianCat O) (tau : FramedLifts O G n rho S) :
    framedCompletionHomToLift O G n rho S
        (framedCompletionLiftToHom O G n rho S tau) = tau := by
  apply Subtype.ext
  exact framedCompletionMap_universalFramedLift O G n rho S tau.1 tau.2

@[simp]
lemma framedCompletionLiftToHom_homToLift
    (S : ProartinianCat O) (f : framedCompletionObject O G n rho ⟶ S) :
    framedCompletionLiftToHom O G n rho S
        (framedCompletionHomToLift O G n rho S f) = f := by
  symm
  apply framedCompletionHom_unique O G n rho S
    (framedCompletionHomToLift O G n rho S f).1
    (framedCompletionHomToLift O G n rho S f).2 f
  rfl

/-- The completed framed representation ring corepresents framed lifts of `rho`. -/
noncomputable def framedCompletionHomEquiv (S : ProartinianCat O) :
    (framedCompletionObject O G n rho ⟶ S) ≃ FramedLifts O G n rho S where
  toFun := framedCompletionHomToLift O G n rho S
  invFun := framedCompletionLiftToHom O G n rho S
  left_inv := framedCompletionLiftToHom_homToLift O G n rho S
  right_inv := framedCompletionHomToLift_liftToHom O G n rho S

end UniversalProperty

end

end Deformation
