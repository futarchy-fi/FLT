/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.Categories
public import FLT.Deformations.DeSmitLenstra.FramedRepresentationRing
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The local completion of the framed representation ring

For a residual representation `ρ : G → GLₙ(k)`, this file constructs the maximal ideal
`m_ρ` of the framed coordinate algebra `O[G,n]`, localizes at `m_ρ`, and completes the
resulting Noetherian local ring at its maximal ideal. This is the algebraic backbone of the
finite-group construction in de Smit--Lenstra, Section 3.

Mathlib proves that the resulting completion is local and adically complete. If the residue field
of `O` is finite, its open quotients are finite because its maximal ideal is finitely generated;
this promotes the completion to `ProartinianCat O` without a general Noetherianity theorem for
adic completions. The continuous universal property remains the next part of dSL-2.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Deformation

noncomputable section

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type v) [Group G] [Finite G]
variable (n : Type w) [Fintype n] [DecidableEq n]

/-- A framed representation ring on finitely many variables over a Noetherian ring is
Noetherian. -/
noncomputable instance framedRepresentationRing_isNoetherian :
    IsNoetherianRing (FramedRepresentationRing O G n) := by
  let e := RingQuot.ringQuotEquivIdealQuotient (FramedRepresentationRelation O G n)
  exact isNoetherianRing_of_ringEquiv _ e.symm

variable (ρ : G →* GL n (ResidueField O))

/-- Evaluation of the framed coordinate algebra at the residual representation. -/
noncomputable def residualRepresentationHom :
    FramedRepresentationRing O G n →ₐ[O] ResidueField O :=
  FramedRepresentationRing.ofRepresentation ρ

omit [IsNoetherianRing O] [Finite G] in
/-- Evaluation at the residual representation is surjective because its restriction to `O`
is the residue map. -/
lemma residualRepresentationHom_surjective :
    Function.Surjective (residualRepresentationHom O G n ρ) := by
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  exact ⟨algebraMap O (FramedRepresentationRing O G n) a, by
    simp [residualRepresentationHom]⟩

/-- The maximal ideal of the framed coordinate algebra selected by `ρ`. -/
noncomputable def residualRepresentationIdeal : Ideal (FramedRepresentationRing O G n) :=
  RingHom.ker (residualRepresentationHom O G n ρ).toRingHom

noncomputable instance residualRepresentationIdeal_isMaximal :
    (residualRepresentationIdeal O G n ρ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (residualRepresentationHom_surjective O G n ρ)

omit [IsNoetherianRing O] [Finite G] in
/-- The residual ideal lies over the maximal ideal of the coefficient ring. -/
lemma residualRepresentationIdeal_comap :
    (residualRepresentationIdeal O G n ρ).comap
      (algebraMap O (FramedRepresentationRing O G n)) = maximalIdeal O := by
  ext x
  simp [residualRepresentationIdeal, residualRepresentationHom,
    IsLocalRing.residue_eq_zero_iff]

/-- The localization of the framed coordinate algebra at the residual ideal. -/
abbrev FramedLocalRing :=
  Localization.AtPrime (residualRepresentationIdeal O G n ρ)

noncomputable instance framedLocalRing_isLocalHom :
    IsLocalHom (algebraMap O (FramedLocalRing O G n ρ)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
  rw [← residualRepresentationIdeal_comap O G n ρ]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  rw [IsScalarTower.algebraMap_apply O (FramedRepresentationRing O G n)
    (FramedLocalRing O G n ρ)]
  change algebraMap O (FramedRepresentationRing O G n) x ∈
      (maximalIdeal (FramedLocalRing O G n ρ)).under
        (FramedRepresentationRing O G n) ↔ _
  have h := IsLocalization.AtPrime.under_maximalIdeal
    (FramedLocalRing O G n ρ) (residualRepresentationIdeal O G n ρ)
  simp only [h]

noncomputable instance framedLocalRing_isResidueAlgebra :
    IsResidueAlgebra O (FramedLocalRing O G n ρ) where
  isSurjective' := by
    let e := IsLocalization.AtPrime.equivQuotMaximalIdeal
      (residualRepresentationIdeal O G n ρ) (FramedLocalRing O G n ρ)
    intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e.symm x)
    obtain ⟨o, ho⟩ := residue_surjective (residualRepresentationHom O G n ρ a)
    refine ⟨o, ?_⟩
    have hx : e (Ideal.Quotient.mk (residualRepresentationIdeal O G n ρ) a) = x := by
      exact (congrArg e ha).trans (e.apply_symm_apply _)
    rw [← hx, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
    change Ideal.Quotient.mk _ (algebraMap O (FramedLocalRing O G n ρ) o) =
      Ideal.Quotient.mk _
        (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n ρ) a)
    rw [Ideal.Quotient.eq,
      IsScalarTower.algebraMap_apply O (FramedRepresentationRing O G n)
        (FramedLocalRing O G n ρ),
      ← map_sub (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n ρ))]
    change algebraMap O (FramedRepresentationRing O G n) o - a ∈
      (maximalIdeal (FramedLocalRing O G n ρ)).under
        (FramedRepresentationRing O G n)
    have h := IsLocalization.AtPrime.under_maximalIdeal
      (FramedLocalRing O G n ρ) (residualRepresentationIdeal O G n ρ)
    rw [h]
    change residualRepresentationHom O G n ρ
      (algebraMap O (FramedRepresentationRing O G n) o - a) = 0
    simp [ho]

noncomputable instance framedLocalRing_isNoetherian :
    IsNoetherianRing (FramedLocalRing O G n ρ) := inferInstance

/-- The maximal-adic completion of the framed local ring. -/
noncomputable abbrev FramedCompletion : Type _ :=
  letI : CommRing (FramedLocalRing O G n ρ) := inferInstance
  AdicCompletion (maximalIdeal (FramedLocalRing O G n ρ)) (FramedLocalRing O G n ρ)

noncomputable instance framedCompletion_isLocalHom :
    IsLocalHom (algebraMap O (FramedCompletion O G n ρ)) := by
  let : CommRing (FramedLocalRing O G n ρ) := inferInstance
  change IsLocalHom (algebraMap O
    (AdicCompletion (maximalIdeal (FramedLocalRing O G n ρ)) (FramedLocalRing O G n ρ)))
  rw [IsScalarTower.algebraMap_eq O (FramedLocalRing O G n ρ)
    (AdicCompletion (maximalIdeal (FramedLocalRing O G n ρ)) (FramedLocalRing O G n ρ))]
  infer_instance

noncomputable instance framedCompletion_isLocalRing :
    IsLocalRing (FramedCompletion O G n ρ) := inferInstance

noncomputable instance framedCompletion_isAdicComplete :
    IsAdicComplete (maximalIdeal (FramedCompletion O G n ρ))
      (FramedCompletion O G n ρ) := inferInstance

noncomputable instance framedCompletion_isResidueAlgebra :
    IsResidueAlgebra O (FramedCompletion O G n ρ) where
  isSurjective' := by
    let : CommRing (FramedLocalRing O G n ρ) := inferInstance
    intro x
    obtain ⟨y, rfl⟩ := (AdicCompletion.residueField_map_bijective
      (FramedLocalRing O G n ρ)).2 x
    obtain ⟨o, ho⟩ := IsResidueAlgebra.algebraMap_surjective O
      (FramedLocalRing O G n ρ) y
    refine ⟨o, ?_⟩
    rw [← ho]
    exact (IsScalarTower.algebraMap_apply O
      (ResidueField (FramedLocalRing O G n ρ))
      (ResidueField (FramedCompletion O G n ρ)) o).symm

noncomputable instance framedCompletion_residueField_finite
    [Finite (ResidueField O)] : Finite (ResidueField (FramedCompletion O G n ρ)) :=
  (IsResidueAlgebra.algEquiv O (FramedCompletion O G n ρ)).toEquiv.finite_iff.mp
    inferInstance

/-- The maximal ideal of the completion is finitely generated, even though no general
Noetherianity instance for adic completions is needed here. -/
lemma framedCompletion_maximalIdeal_fg :
    (maximalIdeal (FramedCompletion O G n ρ)).FG := by
  let : CommRing (FramedLocalRing O G n ρ) := inferInstance
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.FG.map
    (IsNoetherian.noetherian (maximalIdeal (FramedLocalRing O G n ρ)))
    (algebraMap (FramedLocalRing O G n ρ) (FramedCompletion O G n ρ))

/-- The universal matrix representation, transported first to the residual localization and then
to its maximal-adic completion. -/
noncomputable def universalFramedLift : G →* GL n (FramedCompletion O G n ρ) :=
  letI : CommRing (FramedLocalRing O G n ρ) := inferInstance
  (Matrix.GeneralLinearGroup.map
    ((algebraMap (FramedLocalRing O G n ρ)
      (AdicCompletion (maximalIdeal (FramedLocalRing O G n ρ))
        (FramedLocalRing O G n ρ))).comp
      (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n ρ)))).comp
    (universalRepresentation O G n)

section ProartinianObject

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [Finite G]
variable (n : Type u) [Fintype n] [DecidableEq n]
variable [Finite (ResidueField O)] (rho : G →* GL n (ResidueField O))

/-- The completed framed representation ring as a local proartinian `O`-algebra. -/
noncomputable def framedCompletionObject : ProartinianCat O where
  carrier := FramedCompletion O G n rho
  topologicalSpace := (maximalIdeal (FramedCompletion O G n rho)).adicTopology
  isLocalProartinianAlgebra := by
    let : TopologicalSpace (FramedCompletion O G n rho) :=
      (maximalIdeal (FramedCompletion O G n rho)).adicTopology
    let : IsTopologicalRing (FramedCompletion O G n rho) :=
      (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    let : IsLocalRing.IsAdicTopology (FramedCompletion O G n rho) := ⟨rfl⟩
    let : UniformSpace (FramedCompletion O G n rho) :=
      IsTopologicalAddGroup.rightUniformSpace (FramedCompletion O G n rho)
    let : IsUniformAddGroup (FramedCompletion O G n rho) :=
      isUniformAddGroup_of_addCommGroup
    let : IsLinearTopology (FramedCompletion O G n rho)
        (FramedCompletion O G n rho) :=
      Ideal.isLinearTopology (maximalIdeal (FramedCompletion O G n rho))
    let : Finite (ResidueField (FramedCompletion O G n rho)) :=
      framedCompletion_residueField_finite O G n rho
    have hcomplete := (IsAdic.isAdicComplete_iff
      (R := FramedCompletion O G n rho)
      (I := maximalIdeal (FramedCompletion O G n rho))
      (IsLocalRing.IsAdicTopology.isAdic (R := FramedCompletion O G n rho))).mp
        (framedCompletion_isAdicComplete O G n rho)
    let : CompleteSpace (FramedCompletion O G n rho) := hcomplete.1
    let : T2Space (FramedCompletion O G n rho) := hcomplete.2
    let hT1 : T1Space (FramedCompletion O G n rho) :=
      @T2Space.t1Space _ _ hcomplete.2
    let : T0Space (FramedCompletion O G n rho) :=
      (t1Space_iff_t0Space_and_r0Space.mp hT1).1
    let : IsProartinian (FramedCompletion O G n rho) :=
      { isArtinianRing_quotient := fun I hI ↦ by
          obtain ⟨m, -, hm⟩ :=
            (IsLocalRing.hasBasis_maximalIdeal_pow (FramedCompletion O G n rho)).mem_iff.mp
              (hI.mem_nhds (I.zero_mem))
          have hm' : maximalIdeal (FramedCompletion O G n rho) ^ m ≤ I := by
            simpa only [SetLike.coe_subset_coe] using hm
          let : Finite ((FramedCompletion O G n rho) ⧸
              maximalIdeal (FramedCompletion O G n rho)) :=
            framedCompletion_residueField_finite O G n rho
          let : Finite ((FramedCompletion O G n rho) ⧸
              maximalIdeal (FramedCompletion O G n rho) ^ m) :=
            Ideal.finite_quotient_pow (framedCompletion_maximalIdeal_fg O G n rho) m
          let : Finite ((FramedCompletion O G n rho) ⧸ I) :=
            Finite.of_surjective (Ideal.Quotient.factor hm')
              (Ideal.Quotient.factor_surjective hm')
          infer_instance }
    exact ⟨⟩

end ProartinianObject

end

end Deformation
