/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesOverlap
public import FLT.Mazur.WeierstrassModificationGluing

/-!
# Scheme comparison for the scale and horizontal fraction charts

The two chart spectra and their common ratio open form a span isomorphic to
that of the equation modification. Both squares retain all chart functions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The scale fraction spectrum is the actual divided equation chart. -/
def scaleChartIso (hs : IsRegular s) :
    Spec (.of (WeierstrassDilatation.scaleReesChart W s)) ≅
      Spec (.of (WeierstrassDilatation.Coordinate W s b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
      hs).toRingEquiv.toCommRingCatIso.op

/-- The horizontal fraction spectrum is the actual x-direction equation chart. -/
def horizontalChartIso [IsDomain R] (hs : s ≠ 0) :
    Spec (.of (WeierstrassModificationX.horizontalReesChart W s)) ≅
      Spec (.of (WeierstrassModificationX.Coordinate W s b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6
      hs).toRingEquiv.toCommRingCatIso.op

/-- The common fraction ratio open is the common equation open. -/
def horizontalOverlapIso [IsDomain R] (hs : s ≠ 0) :
    Spec (.of (HorizontalScaleOpen W s)) ≅
      Spec (.of (WeierstrassModificationX.XOpen W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (horizontalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6
      hs).toRingEquiv.toCommRingCatIso.op

/-- The ratio open included in the horizontal fraction chart. -/
def horizontalOpenInclusion : Spec (.of (HorizontalScaleOpen W s)) ⟶
    Spec (.of (WeierstrassModificationX.horizontalReesChart W s)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

instance horizontalOpenInclusion_isOpenImmersion :
    IsOpenImmersion (horizontalOpenInclusion W s) :=
  IsOpenImmersion.of_isLocalization (horizontalScale W s)

/-- Inclusion of the horizontal ratio open in the scale fraction chart. -/
def scaleOpenInclusion : Spec (.of (ScaleHorizontalOpen W s)) ⟶
    Spec (.of (WeierstrassDilatation.scaleReesChart W s)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

instance scaleOpenInclusion_isOpenImmersion : IsOpenImmersion (scaleOpenInclusion W s) :=
  IsOpenImmersion.of_isLocalization (scaleHorizontal W s)

/-- The spectrum isomorphism of the actual common fraction opens. -/
irreducible_def fractionOverlapIso [IsDomain R] (hs : s ≠ 0) :
    Spec (.of (HorizontalScaleOpen W s)) ≅ Spec (.of (ScaleHorizontalOpen W s)) :=
  Scheme.Spec.mapIso (scaleHorizontalTransition W s b3 b4 b6 h3 h4 h6
    hs).toRingEquiv.toCommRingCatIso.op

/-- The ratio open mapped into the scale fraction chart by the proved substitution. -/
irreducible_def horizontalOverlapToScale [IsDomain R] (hs : s ≠ 0) :
    Spec (.of (HorizontalScaleOpen W s)) ⟶
      Spec (.of (WeierstrassDilatation.scaleReesChart W s)) :=
  (fractionOverlapIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
    scaleOpenInclusion W s

set_option backward.isDefEq.respectTransparency true in
instance horizontalOverlapToScale_isOpenImmersion [IsDomain R] (hs : s ≠ 0) :
    IsOpenImmersion (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs) := by
  rw [horizontalOverlapToScale_def]
  let _ : IsOpenImmersion (fractionOverlapIso W s b3 b4 b6 h3 h4 h6 hs).hom :=
    IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp _ _

/-- The horizontal chart comparison commutes with the full overlap inclusion. -/
@[reassoc] theorem horizontalOverlapIso_inclusion [IsDomain R] (hs : s ≠ 0) :
    horizontalOpenInclusion W s ≫ (horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom =
      (horizontalOverlapIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationX.xOpenInclusion W s b3 b4 b6 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (horizontalScaleOpenEquiv_base W s b3 b4 b6 h3 h4 h6 hs a).symm

/-- The scale chart comparison commutes with the substituted overlap inclusion. -/
@[reassoc] theorem horizontalOverlapIso_toScale [IsDomain R] (hs : s ≠ 0) :
    horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs ≫
        (scaleChartIso W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs)).hom =
      (horizontalOverlapIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationX.overlapToDivided W s b3 b4 b6 := by
  rw [horizontalOverlapToScale_def, fractionOverlapIso_def]
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ =
    Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change scaleHorizontalTransition W s b3 b4 b6 h3 h4 h6 hs
    (algebraMap _ _ (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
      (IsRegular.of_ne_zero hs) a)) =
    horizontalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationX.overlapForward W s b3 b4 b6 (algebraMap _ _ a))
  rw [WeierstrassModificationX.overlapForward_base, scaleHorizontalTransition_base]

end FLT.Mazur.WeierstrassModificationReesCoordinates
