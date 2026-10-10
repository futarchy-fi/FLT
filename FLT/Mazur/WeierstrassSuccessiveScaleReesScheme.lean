/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveScaleReesChart
public import FLT.Mazur.WeierstrassSuccessiveXSchemeOverlap
public import FLT.Mazur.BlowupReesProper

/-!
# The successive scale chart in the same Rees scheme

The deeper divided chart is the entire standard scale open of the Rees
scheme of the preceding center. Its contraction is the existing refinement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassSuccessiveScale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R) (hπ : IsRegular π)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "ref" => WeierstrassDilatation.refinement W s π
  (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

/-- The actual deeper divided chart is the scale fraction chart as a scheme. -/
def scaleReesSchemeIso : Spec (.of D) ≅
    Spec (.of (scaleReesChart W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (scaleReesChartEquiv W s π b3 b4 b6 hπ).symm.toRingEquiv.toCommRingCatIso.op

/-- The actual scale chart embeds in the Rees projective spectrum. -/
def toReesProj : Spec (.of D) ⟶ BlowupRees.proj I :=
  (scaleReesSchemeIso W s π b3 b4 b6 hπ).hom ≫
    BlowupRees.fractionChartInclusion I (algebraMap R B π) (Ideal.subset_span (by simp))

/-- The comparison gives an open immersion of the actual equation chart. -/
instance toReesProj_isOpenImmersion : IsOpenImmersion (toReesProj W s π b3 b4 b6 hπ) := by
  unfold toReesProj
  infer_instance

/-- The Rees embedding retains the original preceding divided contraction. -/
@[reassoc] theorem toReesProj_contraction :
    toReesProj W s π b3 b4 b6 hπ ≫ BlowupRees.contraction I =
      WeierstrassSuccessiveX.dividedToPrevious W s π b3 b4 b6 := by
  rw [toReesProj, Category.assoc, BlowupRees.fractionChartInclusion_contraction]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply (scaleReesChartEquiv W s π b3 b4 b6 hπ).injective
  change (scaleReesChartEquiv W s π b3 b4 b6 hπ)
      ((scaleReesChartEquiv W s π b3 b4 b6 hπ).symm
        (algebraMap B (BlowupFractionChart.chart I (algebraMap R B π)) a)) = _
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (scaleReesChartEquiv_refinement W s π b3 b4 b6 hπ a).symm

/-- The actual deeper chart fills the entire standard scale open. -/
theorem toReesProj_range :
    (toReesProj W s π b3 b4 b6 hπ).opensRange =
      BlowupRees.generatorOpen I (algebraMap R B π) (Ideal.subset_span (by simp)) := by
  exact (Scheme.Hom.opensRange_comp_of_isIso
    (scaleReesSchemeIso W s π b3 b4 b6 hπ).hom
    (BlowupRees.fractionChartInclusion I (algebraMap R B π)
      (Ideal.subset_span (by simp)))).trans
        (BlowupRees.fractionChartInclusion_range _ _ _)

end FLT.Mazur.WeierstrassSuccessiveScale
