/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineProductCharts
public import FLT.Mazur.PolygonProper
public import FLT.Mazur.ProperDenseOpenIso
public import FLT.Mazur.SmoothCurveValuationStalk

/-!
# Valuation stalks and proper extension on the original glued line

The polynomial charts prove smoothness, reducedness and integrality. Thus a map
from the entire left chart to a proper target extends uniquely across infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- The reciprocal Laurent puncture is dense in the right polynomial chart. -/
theorem overlapRight_denseRange : DenseRange (overlapRight K) :=
  (overlapRight K).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _

/-- The original complete left affine chart is dense in the glued line. -/
theorem left_denseRange : DenseRange (left K) := by
  intro x
  rcases charts_cover K x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure ⟨y, rfl⟩
  · have h : closure (Set.range (overlapRight K)) ⊆
        (right K) ⁻¹' closure (Set.range (left K)) := by
      apply closure_minimal _ (isClosed_closure.preimage (right K).continuous)
      rintro _ ⟨w, rfl⟩
      exact subset_closure ⟨overlapLeft K w,
        congrArg (fun f => f w) (overlap_condition K)⟩
    exact h (overlapRight_denseRange K y)

/-- The glued line is reduced on both of its actual affine charts. -/
instance valuationLine_isReduced : IsReduced (scheme K) := by
  apply (IsReduced.iff_of_openCover _ (ProjectiveLineProductCharts.chartCover K)).mpr
  intro b
  change IsReduced (chart K)
  infer_instance

/-- Its dense integral affine chart proves irreducibility of the whole line. -/
instance valuationLine_irreducibleSpace : IrreducibleSpace (scheme K) := by
  rw [irreducibleSpace_def]
  have h := (IrreducibleSpace.isIrreducible_univ (chart K)).image
    (left K) (left K).continuous.continuousOn
  rw [Set.image_univ] at h
  simpa only [(left_denseRange K).closure_range, Set.top_eq_univ] using h.closure

/-- The original two-chart projective line is integral. -/
instance valuationLine_isIntegral : IsIntegral (scheme K) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- Each original polynomial chart has relative dimension one. -/
theorem chartToBase_smooth_dimension : SmoothOfRelativeDimension 1 (chartToBase K) := by
  change SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap K (Polynomial K))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv K (Fin 1))

/-- The complete glued line is smooth of relative dimension one. -/
instance valuationLine_smooth_dimension : SmoothOfRelativeDimension 1 (toBase K) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (ProjectiveLineProductCharts.chartCover K)).mpr
  intro b
  cases b
  · change SmoothOfRelativeDimension 1 (left K ≫ toBase K)
    rw [left_toBase]; exact chartToBase_smooth_dimension K
  · change SmoothOfRelativeDimension 1 (right K ≫ toBase K)
    rw [right_toBase]; exact chartToBase_smooth_dimension K

/-- Every actual stalk, including infinity, is a valuation ring. -/
instance valuationLine_stalk (x : scheme K) :
    ValuationRing ((scheme K).presheaf.stalk x) :=
  FCurve.smoothCurve_stalk_valuationRing (toBase K) x

/-- Properness also supplies absolute separatedness of the original line. -/
instance valuationLine_separated : (scheme K).IsSeparated := by
  rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from (toBase K)]
  infer_instance

/-- The actual affine chart is a dominant morphism of schemes. -/
instance valuationLine_left_dominant : IsDominant (left K) := ⟨left_denseRange K⟩

/-- A map on the full left chart extends uniquely to every proper relative target. -/
theorem existsUnique_left_extension {B Y : Scheme.{u}}
    (q : scheme K ⟶ B) (p : Y ⟶ B) [IsProper p]
    (g : chart K ⟶ Y) (hg : g ≫ p = left K ≫ q) :
    ∃! f : scheme K ⟶ Y, f ≫ p = q ∧ left K ≫ f = g := by
  obtain ⟨f, hf, hr⟩ := exists_openImmersion_extension_of_valuation_stalks
    q p (left K) g hg
  refine ⟨f, ⟨hf, hr⟩, ?_⟩
  intro f' hf'
  exact ext_of_isDominant_of_isSeparated p (hf'.1.trans hf.symm)
    (left K) (hf'.2.trans hr.symm)

end FLT.Mazur.ProjectiveLine
