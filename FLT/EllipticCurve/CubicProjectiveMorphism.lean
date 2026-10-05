/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveCover

/-!
# Descent of the Weierstrass chart maps to projective space
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open FLT.Mazur.ProjectiveSpace

set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective coordinate normalized to one on each chart. -/
def pivot (b : Bool) : Fin 3 := if b then 1 else 2

/-- Homogeneous coordinates of the two affine charts. -/
def homogeneousCoords (b : Bool) : Fin 3 → Ring W b :=
  if b then ![coord W b 0, 1, coord W b 1] else ![coord W b 0, coord W b 1, 1]

/-- The designated coordinate is one. -/
theorem homogeneousCoords_pivot (b : Bool) : homogeneousCoords W b (pivot b) = 1 := by
  cases b <;> rfl

/-- Pullback of projective coordinate ratios to the affine cubic chart. -/
def projectiveChartRingMap (b : Bool) : chartRing R (Fin 3) (pivot b) →+* Ring W b :=
  chartEval R (Fin 3) (algebraMap R _) (homogeneousCoords W b)
    (pivot b) (homogeneousCoords_pivot W b)

@[simp] theorem projectiveChartRingMap_coordinate (b : Bool) (i : Fin 3) :
    projectiveChartRingMap W b (coordinate R (Fin 3) (pivot b) i) =
      homogeneousCoords W b i :=
  chartEval_coordinate R (Fin 3) _ _ _ _ i

@[simp] theorem projectiveChartRingMap_scalar (b : Bool) (r : R) :
    projectiveChartRingMap W b (chartScalars R (Fin 3) (pivot b) r) =
      algebraMap R _ r :=
  chartEval_scalar R (Fin 3) _ _ _ _ r

private theorem reindex_scalar (e : Fin 3 ≃ Fin 3) (j : Fin 3) (r : R) :
    reindexChartRingMap R e j (chartScalars R (Fin 3) j r) =
      chartScalars R (Fin 3) (e.symm j) r := by
  apply HomogeneousLocalization.val_injective
  simp [reindexChartRingMap, chartScalars, constantsToZero,
    HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- The explicit affine embedding is the map induced by normalized ratios. -/
theorem chartToProjective_eq (b : Bool) :
    chartToProjective W b =
      Spec.map (CommRingCat.ofHom (projectiveChartRingMap W b)) ≫
        chartMap R (Fin 3) (pivot b) := by
  cases b
  · have h := chartMap_reindexIso R (projectiveCoordinateOrder false) (pivot false)
    change chartMap R (Fin 3) 0 ≫ _ = _ at h
    unfold chartToProjective
    rw [affineChartEmbedding_eq]
    change Spec.map _ ≫ (Spec.map _ ≫ chartMap R (Fin 3) 0) ≫ _ = _
    rw [Category.assoc]
    erw [h]
    rw [ ← Category.assoc, ← Spec.map_comp, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply chartRing_hom_ext
    · intro r
      change Ideal.Quotient.mk _ (chartToPolynomial R 2
        (reindexChartRingMap R (projectiveCoordinateOrder false) (pivot false)
          (chartScalars R (Fin 3) (pivot false) r))) = _
      rw [reindex_scalar]
      change Ideal.Quotient.mk _ (chartToPolynomial R 2 (chartScalars R (Fin 3) 0 r)) =
        projectiveChartRingMap W false (chartScalars R (Fin 3) (pivot false) r)
      rw [chartToPolynomial_scalar, projectiveChartRingMap_scalar]
      rfl
    · intro i
      change Ideal.Quotient.mk _ (chartToPolynomial R 2
        (reindexChartRingMap R (projectiveCoordinateOrder false) (pivot false)
          (coordinate R (Fin 3) (pivot false) i))) = _
      rw [reindexChartRingMap_coordinate]
      change Ideal.Quotient.mk _ (chartToPolynomial R 2
        (coordinate R (Fin 3) 0 ((projectiveCoordinateOrder false).symm i))) =
          projectiveChartRingMap W false (coordinate R (Fin 3) (pivot false) i)
      rw [projectiveChartRingMap_coordinate]
      fin_cases i
      · exact congrArg (Ideal.Quotient.mk _) (chartToPolynomial_coordinate R 2 0)
      · exact congrArg (Ideal.Quotient.mk _) (chartToPolynomial_coordinate R 2 1)
      · simp [projectiveCoordinateOrder, homogeneousCoords, coordinate_self]
  · have h := chartMap_reindexIso R (projectiveCoordinateOrder true) (pivot true)
    change chartMap R (Fin 3) 0 ≫ _ = _ at h
    unfold chartToProjective
    rw [affineChartEmbedding_eq]
    change Spec.map _ ≫ (Spec.map _ ≫ chartMap R (Fin 3) 0) ≫ _ = _
    rw [Category.assoc]
    erw [h]
    rw [ ← Category.assoc, ← Spec.map_comp, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply chartRing_hom_ext
    · intro r
      change Ideal.Quotient.mk _ (chartToPolynomial R 2
        (reindexChartRingMap R (projectiveCoordinateOrder true) (pivot true)
          (chartScalars R (Fin 3) (pivot true) r))) = _
      rw [reindex_scalar]
      change Ideal.Quotient.mk _ (chartToPolynomial R 2 (chartScalars R (Fin 3) 0 r)) =
        projectiveChartRingMap W true (chartScalars R (Fin 3) (pivot true) r)
      rw [chartToPolynomial_scalar, projectiveChartRingMap_scalar]
      rfl
    · intro i
      change Ideal.Quotient.mk _ (chartToPolynomial R 2
        (reindexChartRingMap R (projectiveCoordinateOrder true) (pivot true)
          (coordinate R (Fin 3) (pivot true) i))) = _
      rw [reindexChartRingMap_coordinate]
      change Ideal.Quotient.mk _ (chartToPolynomial R 2
        (coordinate R (Fin 3) 0 ((projectiveCoordinateOrder true).symm i))) =
          projectiveChartRingMap W true (coordinate R (Fin 3) (pivot true) i)
      rw [projectiveChartRingMap_coordinate]
      fin_cases i
      · exact congrArg (Ideal.Quotient.mk _) (chartToPolynomial_coordinate R 2 0)
      · simp [projectiveCoordinateOrder, homogeneousCoords, coordinate_self]
      · exact congrArg (Ideal.Quotient.mk _) (chartToPolynomial_coordinate R 2 1)

/-- Restriction of the ordinary projective chart to the Weierstrass overlap. -/
def projectiveOverlapLeft : chartRing R (Fin 3) 2 →+* Overlap W false :=
  (algebraMap (Ring W false) (Overlap W false)).comp (projectiveChartRingMap W false)

/-- Restriction of the infinity projective chart, in ordinary overlap coordinates. -/
def projectiveOverlapRight : chartRing R (Fin 3) 1 →+* Overlap W false :=
  (changeChart W false).toRingHom.comp (projectiveChartRingMap W true)

@[simp] theorem projectiveOverlapLeft_coordinate (i : Fin 3) :
    projectiveOverlapLeft W (coordinate R (Fin 3) 2 i) =
      ![loc W false 0, loc W false 1, 1] i := by
  change algebraMap (Ring W false) (Overlap W false)
    (projectiveChartRingMap W false (coordinate R (Fin 3) (pivot false) i)) = _
  rw [projectiveChartRingMap_coordinate]
  fin_cases i <;> simp [homogeneousCoords, loc]

@[simp] theorem projectiveOverlapRight_coordinate (i : Fin 3) :
    projectiveOverlapRight W (coordinate R (Fin 3) 1 i) =
      ![loc W false 0 * inv W false, 1, inv W false] i := by
  change changeChart W false
    (projectiveChartRingMap W true (coordinate R (Fin 3) (pivot true) i)) = _
  rw [projectiveChartRingMap_coordinate]
  fin_cases i
  · exact changeChart_coord W false 0
  · exact map_one (changeChart W false)
  · exact changeChart_coord W false 1

/-- The Y/Z ratio is invertible on the Weierstrass overlap. -/
theorem projectiveOverlap_unit :
    IsUnit (projectiveOverlapLeft W (coordinate R (Fin 3) 2 1)) := by
  rw [projectiveOverlapLeft_coordinate]
  exact ⟨⟨loc W false 1, inv W false, loc_mul_inv W false, inv_mul_loc W false⟩, rfl⟩

/-- Pullback from the intersection of the Y and Z projective charts. -/
def projectiveOverlapMap : overlapRing R (Fin 3) 2 1 →+* Overlap W false := by
  letI := (toOverlap R (Fin 3) 2 1).toAlgebra
  letI := overlap_isLocalization R (Fin 3) 2 1
  exact IsLocalization.Away.lift (coordinate R (Fin 3) 2 1)
    (g := projectiveOverlapLeft W) (projectiveOverlap_unit W)

/-- The projective overlap map extends the ordinary chart map. -/
theorem projectiveOverlapMap_left :
    (projectiveOverlapMap W).comp (chartOverlapLeft R (Fin 3) 2 1) =
      projectiveOverlapLeft W := by
  let := (toOverlap R (Fin 3) 2 1).toAlgebra
  let := overlap_isLocalization R (Fin 3) 2 1
  exact IsLocalization.Away.lift_comp _ _

/-- The projective overlap map also extends the infinity chart map. -/
theorem projectiveOverlapMap_right :
    (projectiveOverlapMap W).comp (chartOverlapRight R (Fin 3) 2 1) =
      projectiveOverlapRight W := by
  have hleft (z : chartRing R (Fin 3) 2) :=
    DFunLike.congr_fun (projectiveOverlapMap_left W) z
  apply chartRing_hom_ext
  · intro r
    change projectiveOverlapMap W
      (chartOverlapRight R (Fin 3) 2 1 (algebraMap R _ r)) =
        changeChart W false (projectiveChartRingMap W true
          (chartScalars R (Fin 3) (pivot true) r))
    rw [AlgHom.commutes, projectiveChartRingMap_scalar]
    have hc := (changeChart W false).commutes r
    dsimp only [Bool.not] at hc
    refine Eq.trans ?_ hc.symm
    have h := hleft (chartScalars R (Fin 3) 2 r)
    change projectiveOverlapMap W
      (chartOverlapLeft R (Fin 3) 2 1 (algebraMap R _ r)) =
        algebraMap (Ring W false) (Overlap W false)
          (projectiveChartRingMap W false (chartScalars R (Fin 3) (pivot false) r)) at h
    simpa only [AlgHom.commutes, projectiveChartRingMap_scalar,
      ← IsScalarTower.algebraMap_apply R (Ring W false)] using h
  · intro i
    have h := congrArg (projectiveOverlapMap W) (chartOverlap_coordinate R (Fin 3) 2 1 i)
    rw [map_mul] at h
    have hi := hleft (coordinate R (Fin 3) 2 i)
    have hk := hleft (coordinate R (Fin 3) 2 1)
    change projectiveOverlapMap W (chartOverlapLeft R (Fin 3) 2 1 _) = _ at hi hk
    rw [hi, hk] at h
    apply (projectiveOverlap_unit W).mul_right_cancel
    change projectiveOverlapMap W (chartOverlapRight R (Fin 3) 2 1 _) *
      projectiveOverlapLeft W (coordinate R (Fin 3) 2 1) =
        projectiveOverlapRight W (coordinate R (Fin 3) 1 i) *
          projectiveOverlapLeft W (coordinate R (Fin 3) 2 1)
    rw [← h, projectiveOverlapLeft_coordinate, projectiveOverlapRight_coordinate,
      projectiveOverlapLeft_coordinate]
    fin_cases i <;> simp [mul_assoc]

/-- Both affine projective morphisms agree on the actual gluing overlap. -/
theorem chartToProjective_overlap :
    overlapInclusion W false ≫ chartToProjective W false =
      overlapRight W ≫ chartToProjective W true := by
  have hr : (transition W false).toRingHom.comp
      (algebraMap (Ring W true) (Overlap W true)) = (changeChart W false).toRingHom := by
    exact IsLocalization.Away.lift_comp (R := Ring W (!false))
      (S := Overlap W (!false)) _ (by
        change IsUnit (changeChart W false (coord W (!false) 1))
        rw [changeChart_coord]
        exact isUnit_iff_exists_inv.mpr ⟨loc W false 1, inv_mul_loc W false⟩)
  rw [chartToProjective_eq, chartToProjective_eq]
  unfold overlapRight
  rw [overlapIso_hom]
  unfold overlapInclusion
  simp only [Category.assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (projectiveOverlapLeft W)) ≫
      chartMap R (Fin 3) 2 =
    Spec.map (CommRingCat.ofHom (transition W false).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (Overlap W true))) ≫
        Spec.map (CommRingCat.ofHom (projectiveChartRingMap W true)) ≫
          chartMap R (Fin 3) 1
  rw [← Category.assoc (Spec.map _) (Spec.map _), ← Spec.map_comp]
  have hrs : Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (Overlap W true)) ≫
      CommRingCat.ofHom (transition W false).toRingHom) =
        Spec.map (CommRingCat.ofHom (changeChart W false).toRingHom) :=
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hr
  rw [hrs, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (projectiveOverlapLeft W)) ≫ chartMap R (Fin 3) 2 =
    Spec.map (CommRingCat.ofHom (projectiveOverlapRight W)) ≫ chartMap R (Fin 3) 1
  rw [← projectiveOverlapMap_left, ← projectiveOverlapMap_right]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (projectiveOverlapMap W)) ≫ f)
    ((chartOverlapLeft_chartMap R (Fin 3) 2 1).trans
      (chartOverlapRight_chartMap R (Fin 3) 2 1).symm)

/-- The morphism to the projective plane obtained by descent of the two charts. -/
def toProjective : scheme W ⟶ FLT.Mazur.ProjectiveSpace.space R (Fin 3) :=
  pushout.desc (chartToProjective W false) (chartToProjective W true)
    (chartToProjective_overlap W)

/-- The global morphism restricts to the ordinary projective chart map. -/
@[reassoc (attr := simp)] theorem affineChart_toProjective :
    affineChart W ≫ toProjective W = chartToProjective W false :=
  pushout.inl_desc _ _ _

/-- The global morphism restricts to the infinity projective chart map. -/
@[reassoc (attr := simp)] theorem infinityChart_toProjective :
    infinityChart W ≫ toProjective W = chartToProjective W true :=
  pushout.inr_desc _ _ _

/-- Descent preserves the coefficient-base projection. -/
@[reassoc (attr := simp)] theorem toProjective_baseProjection :
    toProjective W ≫ baseProjection R (Fin 3) = toBase W := by
  apply pushout.hom_ext
  · change affineChart W ≫ _ = affineChart W ≫ _
    rw [← Category.assoc, affineChart_toProjective, chartToProjective_baseProjection,
      affineChart_toBase]
  · change infinityChart W ≫ _ = infinityChart W ≫ _
    rw [← Category.assoc, infinityChart_toProjective, chartToProjective_baseProjection,
      infinityChart_toBase]

/-- Every affine cubic coordinate is a pullback of a projective ratio. -/
theorem projectiveChartRingMap_surjective (b : Bool) :
    Function.Surjective (projectiveChartRingMap W b) := by
  let f : MvPolynomial (Fin 2) R →+* chartRing R (Fin 3) (pivot b) :=
    eval₂Hom (chartScalars R (Fin 3) (pivot b))
      (fun i ↦ coordinate R (Fin 3) (pivot b) (projectiveCoordinateOrder b i.succ))
  have hf : (projectiveChartRingMap W b).comp f =
      Ideal.Quotient.mk (Ideal.span {equation W b}) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, f, eval₂Hom_C, projectiveChartRingMap_scalar]
      rfl
    · intro i
      simp only [RingHom.comp_apply, f]
      cases b <;> fin_cases i <;>
        simp [homogeneousCoords, projectiveCoordinateOrder, Equiv.swap_apply_def, coord]
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨f p, DFunLike.congr_fun hf p⟩

/-- Before inclusion of the projective open, each chart map is a closed immersion. -/
instance projectiveChartRingMap_isClosedImmersion (b : Bool) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (projectiveChartRingMap W b))) :=
  IsClosedImmersion.spec_of_surjective _ (projectiveChartRingMap_surjective W b)

/-- Standard projective opens pull back to the prescribed homogeneous coordinates. -/
theorem chartToProjective_preimage_chart (b : Bool) (i : Fin 3) :
    chartToProjective W b ⁻¹ᵁ FLT.Mazur.ProjectiveSpace.chart R (Fin 3) i =
      PrimeSpectrum.basicOpen (homogeneousCoords W b i) := by
  rw [chartToProjective_eq, Scheme.Hom.comp_preimage,
    chartMap_preimage_chart, SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen
    (projectiveChartRingMap W b (coordinate R (Fin 3) (pivot b) i)) = _
  rw [projectiveChartRingMap_coordinate]

end WeierstrassCurve.CubicCharts
