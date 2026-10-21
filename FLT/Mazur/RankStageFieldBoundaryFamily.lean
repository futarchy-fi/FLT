/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFinitePointCore
public import FLT.Mazur.RankStageReducedBoundaryFactors

/-!
# Common full boundary factors for finite families of field tests

Endpoints whose original points have the same exact rank have one common
core, at every order. Their full field-valued maps factor uniquely through its
boundary, and the factors commute with the actual order inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance fieldFamilyOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance fieldFamilyOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance fieldFamilyOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData) {K : Type} [Field K]

/-- One core contains every prescribed field-valued endpoint of the same exact rank. -/
theorem exists_rankStage_field_boundary_family {ι : Type} [Finite ι] (n : ℕ)
    (t : ι → (Spec (.of K) ⟶ J.subscheme))
    (ht : ∀ i, (t i ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈
      exactRank (Over.mk p) n) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k i, ∃! u : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme,
        u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t i := by
  obtain ⟨a, ha, hc⟩ := exists_rankStage_finite_point_core e n
    (fun i ↦ (t i ≫ J.subschemeι) (IsLocalRing.closedPoint K)) ht
  refine ⟨a, ha, fun k i ↦ rankStage_boundary_factor_of_range e n a ha J k (t i) ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
  exact hc k i

/-- Every individual original field test has full factors on some coherent rank-core tower. -/
theorem exists_rankStage_field_boundary_factor (t : Spec (.of K) ⟶ J.subscheme) :
    ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k, ∃! u : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme,
        u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t := by
  obtain ⟨n, hn⟩ := exists_exactRank (Over.mk p)
    ((t ≫ J.subschemeι) (IsLocalRing.closedPoint K))
  obtain ⟨a, ha, hc⟩ := exists_rankStage_field_boundary_family e J n
    (fun _ : Unit ↦ t) (fun _ ↦ hn)
  exact ⟨n, a, ha, fun k ↦ hc k ()⟩

variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)

/-- Independently constructed factors of the same original test commute with exact order maps. -/
theorem rankStage_field_boundary_factors_transition {k l : ℕ} (h : k ≤ l)
    (t : Spec (.of K) ⟶ J.subscheme)
    (u : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme)
    (v : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J l).subscheme)
    (hu : u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t)
    (hv : v ≫ rankStageCoreOriginalBoundaryMap e n a ha J l = t) :
    u ≫ rankStageCoreBoundaryMap e n a ha J h = v := by
  apply rankStage_boundary_factor_ext e n a ha J l
  rw [Category.assoc, rankStageCoreOriginalBoundaryMap_transition, hu, hv]

end FLT.Mazur.EquivalenceRelationOrderedFrames
