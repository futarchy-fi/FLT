/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesYHorizontalScheme
public import FLT.Mazur.WeierstrassModificationReesYScaleOverlap
public import FLT.Mazur.WeierstrassModificationYOpenMaps

/-!
# Scheme comparison for the vertical/scale fraction overlap

The actual ratio opens compare with the equation opens, and their substitution
commutes with both chart comparisons on every function.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The vertical scale ratio open is its original equation open. -/
def verticalScaleSchemeIso : Spec (.of (VerticalScaleOpen W s)) ≅
    Spec (.of (WeierstrassModificationY.ScaleOpen W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (verticalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6
    hs).toRingEquiv.toCommRingCatIso.op

/-- Inclusion of the actual scale ratio open in the vertical fraction chart. -/
def verticalScaleInclusion : Spec (.of (VerticalScaleOpen W s)) ⟶
    Spec (.of (WeierstrassModificationY.verticalReesChart W s)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

/-- The actual fraction substitution on spectra. -/
irreducible_def verticalScaleTransitionIso : Spec (.of (VerticalScaleOpen W s)) ≅
    Spec (.of (ScaleVerticalOpen W s)) :=
  Scheme.Spec.mapIso (scaleVerticalTransition W s b3 b4 b6 h3 h4 h6
    hs).toRingEquiv.toCommRingCatIso.op

/-- The vertical ratio open mapped to the scale fraction chart. -/
def verticalToScale : Spec (.of (VerticalScaleOpen W s)) ⟶
    Spec (.of (WeierstrassDilatation.scaleReesChart W s)) :=
  (verticalScaleTransitionIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (WeierstrassDilatation.scaleReesChart W s) (ScaleVerticalOpen W s)))

/-- The comparison retains the entire vertical chart localization map. -/
@[reassoc] theorem verticalScaleSchemeIso_inclusion :
    verticalScaleInclusion W s ≫ (verticalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom =
      (verticalScaleSchemeIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        PrincipalAffineRefinement.inclusion
          (WeierstrassModificationY.coord W s b3 b4 b6 0) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (verticalScaleOpenEquiv_base W s b3 b4 b6 h3 h4 h6 hs a).symm

/-- The comparison retains the entire substitution to the scale chart. -/
@[reassoc] theorem verticalScaleSchemeIso_toChart :
    verticalToScale W s b3 b4 b6 h3 h4 h6 hs ≫
        (scaleChartIso W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs)).hom =
      (verticalScaleSchemeIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationY.scaleToDivided W s b3 b4 b6 := by
  rw [verticalToScale, verticalScaleTransitionIso_def,
    WeierstrassModificationY.scaleToDivided_eq]
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact scaleVerticalTransition_base W s b3 b4 b6 h3 h4 h6 hs a

end FLT.Mazur.WeierstrassModificationReesCoordinates
