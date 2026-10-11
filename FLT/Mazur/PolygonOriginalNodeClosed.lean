/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalNodePoint

/-!
# Closedness of the specified original polygon nodes

The coordinate quotient defines an actual closed immersion into the glued
stage: its composite with the separated structure map is already a closed
immersion. Thus the specified node, and its complete-family image, are closed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- The original coefficient map onto the coordinate quotient is surjective. -/
theorem stageNodeQuotient_scalars_surjective :
    Function.Surjective
      (@algebraMap (Ring K m) (ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m))
        inferInstance inferInstance inferInstance) := by
  intro a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (coordinateQuotientEquiv (parameter K m) a)
  refine ⟨r, (coordinateQuotientEquiv (parameter K m)).injective ?_⟩
  exact ((coordinateQuotientEquiv (parameter K m)).commutes r).trans hr

/-- The actual coordinate quotient inclusion in the original glued stage. -/
def originalStageNodeInclusion (i : Fin n) :
    Spec (.of (ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m))) ⟶
      (family K m n h).left :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coordinateIdeal (parameter K m)))) ≫
    PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i

/-- The node inclusion retains the original coefficient map. -/
@[reassoc] theorem originalStageNodeInclusion_base (i : Fin n) :
    originalStageNodeInclusion K m n h i ≫ (family K m n h).hom =
      Spec.map (CommRingCat.ofHom (algebraMap (Ring K m)
        (ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m)))) := by
  change (Spec.map _ ≫ PolygonInfinitesimal.chart _ _ n h i) ≫
    PolygonInfinitesimal.toBase _ _ n h = _
  rw [Category.assoc, PolygonInfinitesimal.chart_toBase]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- Separatedness makes the coordinate quotient an actual closed immersion into the stage. -/
instance originalStageNodeInclusion_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (originalStageNodeInclusion K m n h i) := by
  have : IsClosedImmersion (originalStageNodeInclusion K m n h i ≫ (family K m n h).hom) := by
    rw [originalStageNodeInclusion_base]
    exact IsClosedImmersion.spec_of_surjective _ (stageNodeQuotient_scalars_surjective K m)
  exact IsClosedImmersion.of_comp _ (family K m n h).hom

/-- The coordinate quotient has exactly the specified original node as its image. -/
theorem originalStageNodeInclusion_range (i : Fin n) :
    Set.range (originalStageNodeInclusion K m n h i) = {originalStageNode K n h m i} := by
  have he : Set.range (PrimeSpectrum.comap
      (S := ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m))
      (Ideal.Quotient.mk (coordinateIdeal (parameter K m)))) =
        {stageNodePoint K m} := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_eq_singleton]
    rfl
  change Set.range (fun x ↦ PolygonInfinitesimal.chart _ _ n h i (Spec.map _ x)) = _
  have hr := Set.range_comp
    (fun x : PrimeSpectrum (ChartRing (parameter K m)) ↦
      PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i x)
    (PrimeSpectrum.comap
      (S := ChartRing (parameter K m) ⧸ coordinateIdeal (parameter K m))
      (Ideal.Quotient.mk (coordinateIdeal (parameter K m))))
  rw [he, Set.image_singleton] at hr
  exact hr

/-- The specified node is closed in the entire actual stage. -/
theorem originalStageNode_isClosed (i : Fin n) : IsClosed {originalStageNode K n h m i} := by
  rw [← originalStageNodeInclusion_range K m n h i]
  exact (originalStageNodeInclusion K m n h i).isClosedEmbedding.isClosed_range

variable [NeZero n]

/-- The chosen node is closed in the actual complete candidate. -/
theorem completeNode_isClosed (i : Fin n) : IsClosed {completeNode K n h i} := by
  let _ := originalStageToCompatibleProj_isClosedImmersion K n h 0
  have hc := (originalStageToCompatibleProj K n h 0).isClosedEmbedding.isClosedMap
    _ (originalStageNode_isClosed K 0 n h i)
  simpa only [Set.image_singleton, completeNode] using hc

end FLT.Mazur.PolygonInfinitesimalStages
