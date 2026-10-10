/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYScaleLocalization
public import FLT.Mazur.WeierstrassModificationYHorizontalLocalization
public import FLT.Mazur.WeierstrassModificationYContractionOverlap
public import FLT.Mazur.WeierstrassModificationYCover
public import FLT.Mazur.WeierstrassModificationGluing

/-!
# The y-direction cover maps openly to the two-chart modification

Each member of the actual y-chart cover is isomorphic to a principal open
in one of the already glued charts. Its contraction agrees with that of the
y-chart. Descending these two maps to a single map on the whole y-chart still
requires checking their compatibility over the intersection of the cover.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The actual isomorphism from the y-chart scale open to the divided vertical open. -/
def scaleIso : Spec (.of (ScaleOpen W s b3 b4 b6)) ≅
    Spec (.of (DividedVertical W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (scaleEquiv W s b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The actual isomorphism from the y-chart horizontal open to the x-chart slope open. -/
def horizontalIso : Spec (.of (HorizontalOpen W s b3 b4 b6)) ≅
    Spec (.of (XVertical W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (horizontalEquiv W s b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The scale open maps openly into the divided chart. -/
def scaleToDivided : Spec (.of (ScaleOpen W s b3 b4 b6)) ⟶
    Spec (.of (WeierstrassDilatation.Coordinate W s b3 b4 b6)) :=
  (scaleIso W s b3 b4 b6).hom ≫
    PrincipalAffineRefinement.inclusion (WeierstrassDilatation.y W s b3 b4 b6)

/-- The horizontal open maps openly into the x-direction chart. -/
def horizontalToX : Spec (.of (HorizontalOpen W s b3 b4 b6)) ⟶
    Spec (.of (WeierstrassModificationX.Coordinate W s b3 b4 b6)) :=
  (horizontalIso W s b3 b4 b6).hom ≫
    PrincipalAffineRefinement.inclusion (WeierstrassModificationX.v W s b3 b4 b6)

instance scaleToDivided_isOpenImmersion : IsOpenImmersion (scaleToDivided W s b3 b4 b6) := by
  dsimp [scaleToDivided]
  infer_instance

instance horizontalToX_isOpenImmersion : IsOpenImmersion (horizontalToX W s b3 b4 b6) := by
  dsimp [horizontalToX]
  infer_instance

/-- The open map is the spectrum of the original scale-ratio evaluation. -/
theorem scaleToDivided_eq : scaleToDivided W s b3 b4 b6 =
    Spec.map (CommRingCat.ofHom (toDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (scaleUnit W s b3 b4 b6) (scaleUnit_val W s b3 b4 b6).symm).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change scaleForward W s b3 b4 b6 (algebraMap _ _ z) = _
  exact scaleForward_base W s b3 b4 b6 z

/-- The other open map is the spectrum of the original horizontal-ratio evaluation. -/
theorem horizontalToX_eq : horizontalToX W s b3 b4 b6 =
    Spec.map (CommRingCat.ofHom (toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (horizontalUnit W s b3 b4 b6) (horizontalUnit_val W s b3 b4 b6).symm).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change horizontalForward W s b3 b4 b6 (algebraMap _ _ z) = _
  exact horizontalForward_base W s b3 b4 b6 z

/-- The scale member of the y-cover maps openly into the constructed modification. -/
def scaleToModification : Spec (.of (ScaleOpen W s b3 b4 b6)) ⟶
    WeierstrassModificationX.modification W s b3 b4 b6 :=
  scaleToDivided W s b3 b4 b6 ≫ WeierstrassModificationX.dividedChart W s b3 b4 b6

/-- The horizontal member of the y-cover maps openly into the constructed modification. -/
def horizontalToModification : Spec (.of (HorizontalOpen W s b3 b4 b6)) ⟶
    WeierstrassModificationX.modification W s b3 b4 b6 :=
  horizontalToX W s b3 b4 b6 ≫ WeierstrassModificationX.xChart W s b3 b4 b6

instance scaleToModification_isOpenImmersion :
    IsOpenImmersion (scaleToModification W s b3 b4 b6) := by
  dsimp [scaleToModification]
  infer_instance

instance horizontalToModification_isOpenImmersion :
    IsOpenImmersion (horizontalToModification W s b3 b4 b6) := by
  dsimp [horizontalToModification]
  infer_instance

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The scale member of the cover contracts to the same original curve point. -/
@[reassoc] theorem scaleToModification_contraction :
    scaleToModification W s b3 b4 b6 ≫
        WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
      PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) ≫
        toCurve W s b3 b4 b6 h3 h4 h6 := by
  rw [scaleToModification, Category.assoc, WeierstrassModificationX.dividedChart_contraction,
    scaleToDivided_eq]
  exact toDivided_toCurve W s b3 b4 b6 h3 h4 h6 _ _ _

/-- The horizontal member of the cover contracts to the same original curve point. -/
@[reassoc] theorem horizontalToModification_contraction :
    horizontalToModification W s b3 b4 b6 ≫
        WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
      PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) ≫
        toCurve W s b3 b4 b6 h3 h4 h6 := by
  rw [horizontalToModification, Category.assoc, WeierstrassModificationX.xChart_contraction,
    horizontalToX_eq]
  exact toX_toCurve W s b3 b4 b6 h3 h4 h6 _ _ _

end FLT.Mazur.WeierstrassModificationY
