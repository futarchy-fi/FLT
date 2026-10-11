/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationCenterCharts
public import FLT.Mazur.WeierstrassIntegralChartIntersection
public import FLT.Mazur.ClosedIdealAffineCoverDescent

/-!
# The actual modification center as an ideal on the whole integral cubic

The ideals (s,X,Y) descend along the original projective atlas. This constructs
an ideal sheaf with precisely the original affine center and empty X/Y-chart
restrictions, retaining all nilpotents and arbitrary coefficient rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.IdealSheafData

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)

/-- The full ideal sheaf of the modification center on a single original chart. -/
def modificationChartCenterSheaf (j : Fin 3) : (chartScheme W j).IdealSheafData :=
  BaseAdicThickening.baseIdeal (.of (Coordinate W j)) (modificationChartCenter W s j)

/-- The chart ideals coincide on the genuine categorical chart intersections. -/
theorem modificationChartCenterSheaf_overlap (j k : Fin 3) :
    (modificationChartCenterSheaf W s j).comap
        (pullback.fst (integralCurveChart W j) (integralCurveChart W k)) =
      (modificationChartCenterSheaf W s k).comap
        (pullback.snd (integralCurveChart W j) (integralCurveChart W k)) := by
  have ht : chartTransition W j k ≫ overlapInclusion W k j =
      Spec.map (CommRingCat.ofHom (transitionBase W j k).toRingHom) := by
    apply (cancel_mono (integralCurveChart W k)).mp
    rw [Category.assoc, integralCurveChart_compatibility, integralCurve_output_transition]
  have h : (modificationChartCenterSheaf W s j).comap (overlapInclusion W j k) =
      (modificationChartCenterSheaf W s k).comap
        (Spec.map (CommRingCat.ofHom (transitionBase W j k).toRingHom)) := by
    change (BaseAdicThickening.baseIdeal _ _).comap (Spec.map _) = _
    rw [BaseAdicThickening.baseIdeal_comap_specMap,
      modificationChartCenterSheaf, BaseAdicThickening.baseIdeal_comap_specMap]
    exact congrArg (BaseAdicThickening.baseIdeal (.of (Overlap W j k)))
      (modificationChartCenter_overlap W s j k).symm
  rw [← integralChartIntersectionIso_fst, ← ht, ← integralChartIntersectionIso_snd,
    comap_comp, comap_comp] at h
  have hi := congrArg
    (fun I => I.comap (integralChartIntersectionIso W j k).inv) h
  simpa only [← comap_comp, Iso.inv_hom_id_assoc] using hi

/-- The actual center ideals form compatible full ideals on the original cover. -/
def modificationCenterCompatibleIdeals :
    ClosedIdealCover.CompatibleIdeals (integralCurveOpenCover W) :=
  ⟨fun j => modificationChartCenterSheaf W s j.down,
    fun j k => modificationChartCenterSheaf_overlap W s j.down k.down⟩

/-- The global scheme-theoretic modification center on the unchanged integral cubic. -/
def modificationCenterSheaf : (integralCurve W).IdealSheafData :=
  ClosedIdealCover.descendIdeal (integralCurveOpenCover W)
    (modificationCenterCompatibleIdeals W s)

/-- Restricting the constructed center recovers each full original chart ideal. -/
theorem modificationCenterSheaf_chart (j : Fin 3) :
    (modificationCenterSheaf W s).comap (integralCurveChart W j) =
      modificationChartCenterSheaf W s j :=
  ClosedIdealCover.descendIdeal_restrict (integralCurveOpenCover W)
    (modificationCenterCompatibleIdeals W s) ⟨j⟩

/-- The center is scheme-theoretically empty on the normalized X and Y charts. -/
theorem modificationCenterSheaf_chart_eq_top (j : Fin 3) (hj : j = 0 ∨ j = 1) :
    (modificationCenterSheaf W s).comap (integralCurveChart W j) = ⊤ := by
  rw [modificationCenterSheaf_chart, modificationChartCenterSheaf,
    modificationChartCenter_eq_top W s j hj]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [BaseAdicThickening.baseIdeal_top, Ideal.map_top, ideal_top, Pi.top_apply]

end FLT.Mazur.WeierstrassIntegralChart
