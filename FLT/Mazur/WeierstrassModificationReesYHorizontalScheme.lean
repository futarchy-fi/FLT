/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesSchemeOverlap
public import FLT.Mazur.WeierstrassModificationReesYHorizontalOverlap
public import FLT.Mazur.WeierstrassModificationYOpenMaps

/-!
# Scheme comparison for the vertical/horizontal fraction overlap

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

/-- The vertical fraction spectrum is the actual y-direction equation chart. -/
def verticalChartIso : Spec (.of (WeierstrassModificationY.verticalReesChart W s)) ≅
    Spec (.of (WeierstrassModificationY.Coordinate W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6
    h3 h4 h6 hs).toRingEquiv.toCommRingCatIso.op

/-- The vertical horizontal ratio open is its original equation open. -/
def verticalHorizontalSchemeIso : Spec (.of (VerticalHorizontalOpen W s)) ≅
    Spec (.of (WeierstrassModificationY.HorizontalOpen W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (verticalHorizontalOpenEquiv W s b3 b4 b6 h3 h4 h6
    hs).toRingEquiv.toCommRingCatIso.op

/-- Inclusion of the actual horizontal ratio open in the vertical fraction chart. -/
def verticalHorizontalInclusion : Spec (.of (VerticalHorizontalOpen W s)) ⟶
    Spec (.of (WeierstrassModificationY.verticalReesChart W s)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

/-- The actual fraction substitution on spectra. -/
irreducible_def verticalHorizontalTransitionIso : Spec (.of (VerticalHorizontalOpen W s)) ≅
    Spec (.of (HorizontalVerticalOpen W s)) :=
  Scheme.Spec.mapIso (horizontalVerticalTransition W s b3 b4 b6 h3 h4 h6
    hs).toRingEquiv.toCommRingCatIso.op

/-- The vertical ratio open mapped to the horizontal fraction chart. -/
def verticalToHorizontal : Spec (.of (VerticalHorizontalOpen W s)) ⟶
    Spec (.of (WeierstrassModificationX.horizontalReesChart W s)) :=
  (verticalHorizontalTransitionIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (WeierstrassModificationX.horizontalReesChart W s) (HorizontalVerticalOpen W s)))

/-- The comparison retains the entire vertical chart localization map. -/
@[reassoc] theorem verticalHorizontalSchemeIso_inclusion :
    verticalHorizontalInclusion W s ≫ (verticalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom =
      (verticalHorizontalSchemeIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        PrincipalAffineRefinement.inclusion
          (WeierstrassModificationY.coord W s b3 b4 b6 1) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (verticalHorizontalOpenEquiv_base W s b3 b4 b6 h3 h4 h6 hs a).symm

/-- The comparison retains the entire substitution to the horizontal chart. -/
@[reassoc] theorem verticalHorizontalSchemeIso_toChart :
    verticalToHorizontal W s b3 b4 b6 h3 h4 h6 hs ≫
        (horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom =
      (verticalHorizontalSchemeIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationY.horizontalToX W s b3 b4 b6 := by
  rw [verticalToHorizontal, verticalHorizontalTransitionIso_def,
    WeierstrassModificationY.horizontalToX_eq]
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact horizontalVerticalTransition_base W s b3 b4 b6 h3 h4 h6 hs a

end FLT.Mazur.WeierstrassModificationReesCoordinates
