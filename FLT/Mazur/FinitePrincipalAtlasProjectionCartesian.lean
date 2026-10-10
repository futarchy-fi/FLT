/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasProjection

/-!
# Cartesian original chart squares of finite-atlas projections

The original common-union recovery identifies the full inverse image of
each glued chart with the corresponding original affine open.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv chartAlgebra principalRepresentative

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R)
  [LocallyOfFiniteType f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f

local notation "OccurrenceStage" => PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E

local notation "AP" => principalOccurrenceAmbientProjection (dst := D) (a := AA) (b := BB) E

local notation "CU" => principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E

local notation "BJ" => principalOccurrenceGluingBijective (dst := D) (a := AA) (b := BB) E

local notation "GD" => principalOccurrenceStageGlueData (dst := D) (a := AA) (b := BB) E

/-- The inverse image of a whole glued chart is exactly the original affine chart. -/
theorem finitePrincipalAtlasProjection_preimage
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (i : Shrink.{u} ι),
      finitePrincipalAtlasProjection U f hU x ⁻¹'
          Set.range ((GD x).ι i) =
        Set.range (U ((equivShrink.{u} ι).symm i)).2.fromSpec := by
  intro _ _ _ _ x i
  let G := GD x
  let q := finitePrincipalAtlasProjection U f hU x
  have hq (j : Shrink.{u} ι) : (U ((equivShrink.{u} ι).symm j)).2.fromSpec ≫ q =
      AP x.val ((equivShrink.{u} ι).symm j) ≫ G.ι j := by
    exact (finitePrincipalAtlasProjection_chart U f hU x j).trans
      (by unfold principalOccurrenceOriginalGluedChart; rfl)
  ext z
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨j, w, rfl⟩ := (finitePrincipalAtlasOriginalCover U hU).exists_eq z
    change Shrink.{u} ι at j
    have he : G.ι j (AP x.val ((equivShrink.{u} ι).symm j) w) = G.ι i v := by
      exact (congrArg
        (fun k : Spec Γ(X, (U ((equivShrink.{u} ι).symm j)).1) ⟶ G.glued ↦ k w)
        (hq j)).symm.trans hv.symm
    obtain ⟨r, hr, _⟩ := (G.ι_eq_iff j i _ v).mp he
    have hw : w ∈ AP x.val ((equivShrink.{u} ι).symm j) ⁻¹ᵁ
        CU x.val (BJ x)
          ((equivShrink.{u} ι).symm j) ((equivShrink.{u} ι).symm i) := by
      change AP x.val ((equivShrink.{u} ι).symm j) w ∈
        CU x.val (BJ x) ((equivShrink.{u} ι).symm j) ((equivShrink.{u} ι).symm i)
      have hr' :
          (CU x.val (BJ x) ((equivShrink.{u} ι).symm j) ((equivShrink.{u} ι).symm i)).ι r =
            AP x.val ((equivShrink.{u} ι).symm j) w := hr
      exact (congrArg (fun z ↦ z ∈
        CU x.val (BJ x) ((equivShrink.{u} ι).symm j) ((equivShrink.{u} ι).symm i)) hr').mp
          r.property
    rw [principalOccurrenceCommonUnion_preimage, atlasPrincipalOriginalCommonUnion_eq U f] at hw
    change (U ((equivShrink.{u} ι).symm j)).2.fromSpec w ∈ (U ((equivShrink.{u} ι).symm i)).1 at hw
    rw [← (U ((equivShrink.{u} ι).symm i)).2.opensRange_fromSpec] at hw
    exact hw
  · rintro ⟨w, rfl⟩
    exact ⟨AP x.val ((equivShrink.{u} ι).symm i) w,
      (congrArg (fun k : Spec Γ(X, (U ((equivShrink.{u} ι).symm i)).1) ⟶ G.glued ↦ k w)
        (hq i)).symm⟩

/-- The original whole affine chart is the base change of its finite-stage chart. -/
theorem finitePrincipalAtlasProjection_isPullback
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (i : Shrink.{u} ι),
      IsPullback (AP x.val ((equivShrink.{u} ι).symm i))
        (U ((equivShrink.{u} ι).symm i)).2.fromSpec ((GD x).ι i)
        (finitePrincipalAtlasProjection U f hU x) := by
  intro _ _ _ _ x i
  refine @IsOpenImmersion.isPullback _ _ _ _
    (AP x.val ((equivShrink.{u} ι).symm i))
    (U ((equivShrink.{u} ι).symm i)).2.fromSpec ((GD x).ι i)
    (finitePrincipalAtlasProjection U f hU x)
    (U ((equivShrink.{u} ι).symm i)).2.isOpenImmersion_fromSpec
    ((GD x).ι_isOpenImmersion i) ?_ ?_
  · exact (finitePrincipalAtlasProjection_chart U f hU x i).trans
      (by unfold principalOccurrenceOriginalGluedChart; rfl)
  · ext z
    exact Set.ext_iff.mp (finitePrincipalAtlasProjection_preimage U f hU x i) z

end FLT.Mazur.Approximation
