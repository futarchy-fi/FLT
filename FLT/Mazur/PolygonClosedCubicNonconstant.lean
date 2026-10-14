/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionSurjective
public import FLT.Mazur.WeierstrassOriginIdealAffine

/-!
# Nonconstancy of the global closed-cubic comparison

The original origin lies outside the Z chart, whereas every omitted component
maps into it. These give distinct points in the specified Cartesian cubic.
Surjectivity then gives distinct images of the actual one-gon comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "z" => completePointCubicChangedZero K n h (completeClosedBase K) i
local notation "a" => Over.Hom.left (closedPointContractionComparison K n h i)

/-- The omitted component's image differs from the original cubic origin. -/
theorem closedPointCubic_origin_ne_omitted {j : Fin n} (hj : j ≠ i)
    (x : Spec (.of K)) (y : ProjectiveLine.scheme K) :
    z x ≠ closedPointComponentToCubic K n h i j y := by
  intro he
  have he' := congrArg (fun t ↦ (pullback.fst (integralCurveStructure W)
    (completeClosedBase K ≫ (Spec (.of (PowerSeries K))).toSpecΓ)) t) he
  change (z ≫ pullback.fst _ _) x =
    (closedPointComponentToCubic K n h i j ≫ pullback.fst _ _) y at he'
  rw [completePointCubicChangedZero_fst, closedPointComponentToCubic_fst] at he'
  apply originSection_notMem_affine W
    ((completeClosedBase K ≫ (Spec (.of (PowerSeries K))).toSpecΓ) x)
  refine ⟨closedPointOmittedAffineMap K n h i hj y, ?_⟩
  exact (congrArg (fun f ↦ f y)
    (closedPointOmittedAffineMap_inclusion K n h i hj)).trans he'.symm

/-- The actual global comparison has two different images over the original field. -/
theorem closedPointContractionComparison_nonconstant :
    ∃ x y : (PolygonAtlas.polygon K 1).left, a x ≠ a y := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h
  obtain ⟨j, hj⟩ := exists_ne i
  let x : Spec (.of K) := default
  let y := ProjectiveLine.zero K x
  obtain ⟨u, hu⟩ := (closedPointContractionComparison_surjective K n h i).surj (z x)
  obtain ⟨v, hv⟩ := (closedPointContractionComparison_surjective K n h i).surj
    (closedPointComponentToCubic K n h i j y)
  exact ⟨u, v, by rw [hu, hv]; exact closedPointCubic_origin_ne_omitted K n h i hj x y⟩

end FLT.Mazur.PolygonInfinitesimalStages
