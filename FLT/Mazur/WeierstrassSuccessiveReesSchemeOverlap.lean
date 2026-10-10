/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesOverlap
public import FLT.Mazur.WeierstrassSuccessiveXGluing

/-!
# Scheme comparison for the scale and horizontal fraction charts

The two chart spectra and their common ratio open form a span isomorphic to
that of the equation modification. Both squares retain all chart functions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The scale fraction spectrum is the actual divided equation chart. -/
def scaleChartIso (hπ : IsRegular π) :
    Spec (.of (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)) ≅
      Spec (.of (WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (WeierstrassSuccessiveScale.scaleReesChartEquiv W s π b3 b4 b6
      hπ).toRingEquiv.toCommRingCatIso.op

/-- The horizontal fraction spectrum is the actual x-direction equation chart. -/
def horizontalChartIso [IsDomain R] (hπ : π ≠ 0) :
    Spec (.of (WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6)) ≅
      Spec (.of (WeierstrassSuccessiveX.Coordinate W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (WeierstrassSuccessiveX.horizontalReesChartEquiv W s π b3 b4 b6
      hπ).toRingEquiv.toCommRingCatIso.op

/-- The common fraction ratio open is the common equation open. -/
def horizontalOverlapIso [IsDomain R] (hπ : π ≠ 0) :
    Spec (.of (HorizontalScaleOpen W s π b3 b4 b6)) ≅
      Spec (.of (WeierstrassSuccessiveX.XOpen W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso (horizontalScaleOpenEquiv W s π b3 b4 b6
      hπ).toRingEquiv.toCommRingCatIso.op

/-- The ratio open included in the horizontal fraction chart. -/
def horizontalOpenInclusion : Spec (.of (HorizontalScaleOpen W s π b3 b4 b6)) ⟶
    Spec (.of (WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

instance horizontalOpenInclusion_isOpenImmersion :
    IsOpenImmersion (horizontalOpenInclusion W s π b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (horizontalScale W s π b3 b4 b6)

/-- Inclusion of the horizontal ratio open in the scale fraction chart. -/
def scaleOpenInclusion : Spec (.of (ScaleHorizontalOpen W s π b3 b4 b6)) ⟶
    Spec (.of (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

instance scaleOpenInclusion_isOpenImmersion : IsOpenImmersion (scaleOpenInclusion W s π b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (scaleHorizontal W s π b3 b4 b6)

/-- The spectrum isomorphism of the actual common fraction opens. -/
irreducible_def fractionOverlapIso [IsDomain R] (hπ : π ≠ 0) :
    Spec (.of (HorizontalScaleOpen W s π b3 b4 b6)) ≅
      Spec (.of (ScaleHorizontalOpen W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso (scaleHorizontalTransition W s π b3 b4 b6
    hπ).toRingEquiv.toCommRingCatIso.op

/-- The ratio open mapped into the scale fraction chart by the proved substitution. -/
irreducible_def horizontalOverlapToScale [IsDomain R] (hπ : π ≠ 0) :
    Spec (.of (HorizontalScaleOpen W s π b3 b4 b6)) ⟶
      Spec (.of (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)) :=
  (fractionOverlapIso W s π b3 b4 b6 hπ).hom ≫
    scaleOpenInclusion W s π b3 b4 b6

set_option backward.isDefEq.respectTransparency true in
instance horizontalOverlapToScale_isOpenImmersion [IsDomain R] (hπ : π ≠ 0) :
    IsOpenImmersion (horizontalOverlapToScale W s π b3 b4 b6 hπ) := by
  rw [horizontalOverlapToScale_def]
  let _ : IsOpenImmersion (fractionOverlapIso W s π b3 b4 b6 hπ).hom :=
    IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp _ _

/-- The horizontal chart comparison commutes with the full overlap inclusion. -/
@[reassoc] theorem horizontalOverlapIso_inclusion [IsDomain R] (hπ : π ≠ 0) :
    horizontalOpenInclusion W s π b3 b4 b6 ≫ (horizontalChartIso W s π b3 b4 b6 hπ).hom =
      (horizontalOverlapIso W s π b3 b4 b6 hπ).hom ≫
        WeierstrassSuccessiveX.xOpenInclusion W s π b3 b4 b6 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (horizontalScaleOpenEquiv_base W s π b3 b4 b6 hπ a).symm

/-- The scale chart comparison commutes with the substituted overlap inclusion. -/
@[reassoc] theorem horizontalOverlapIso_toScale [IsDomain R] (hπ : π ≠ 0) :
    horizontalOverlapToScale W s π b3 b4 b6 hπ ≫
        (scaleChartIso W s π b3 b4 b6 (IsRegular.of_ne_zero hπ)).hom =
      (horizontalOverlapIso W s π b3 b4 b6 hπ).hom ≫
        WeierstrassSuccessiveX.overlapToDivided W s π b3 b4 b6 := by
  rw [horizontalOverlapToScale_def, fractionOverlapIso_def]
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ =
    Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change scaleHorizontalTransition W s π b3 b4 b6 hπ
    (algebraMap _ _ (WeierstrassSuccessiveScale.scaleReesChartEquiv W s π b3 b4 b6
      (IsRegular.of_ne_zero hπ) a)) =
    horizontalScaleOpenEquiv W s π b3 b4 b6 hπ
      (WeierstrassSuccessiveX.overlapForward W s π b3 b4 b6 (algebraMap _ _ a))
  rw [WeierstrassSuccessiveX.overlapForward_base, scaleHorizontalTransition_base]

end FLT.Mazur.WeierstrassSuccessiveRees
