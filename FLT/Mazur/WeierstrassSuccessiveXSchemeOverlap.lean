/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXLocalization

/-!
# The actual scheme overlap of successive modification charts

The localized algebra equivalence gives an isomorphism of actual principal
opens. Both maps to the preceding divided chart agree on this overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)

/-- The deeper divided chart contracts by the already constructed refinement. -/
def dividedToPrevious : Spec (.of D) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (WeierstrassDilatation.refinement W s π
    (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl).toRingHom)

/-- Inclusion of the successive incidence principal open. -/
def xOpenInclusion : Spec (.of (XOpen W s π b3 b4 b6)) ⟶
    Spec (.of (Coordinate W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Coordinate W s π b3 b4 b6) _))

/-- Inclusion of the new divided principal open. -/
def dividedOpenInclusion : Spec (.of (DividedOpen W s π b3 b4 b6)) ⟶ Spec (.of D) :=
  Spec.map (CommRingCat.ofHom (algebraMap D _))

instance xOpenInclusion_isOpenImmersion :
    IsOpenImmersion (xOpenInclusion W s π b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (coord W s π b3 b4 b6 0)

instance dividedOpenInclusion_isOpenImmersion :
    IsOpenImmersion (dividedOpenInclusion W s π b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (WeierstrassDilatation.x W (s * π) b3 b4 b6)

/-- The actual two principal opens are isomorphic. -/
def overlapIso : Spec (.of (XOpen W s π b3 b4 b6)) ≅
    Spec (.of (DividedOpen W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso (overlapEquiv W s π b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The forward substitution retains the preceding divided coordinates. -/
theorem dividedToXOpen_refinement :
    (dividedToXOpen W s π b3 b4 b6).comp
        (WeierstrassDilatation.refinement W s π
          (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl) =
      (IsScalarTower.toAlgHom R _ (XOpen W s π b3 b4 b6)).comp
        (fromDivided W s π b3 b4 b6) := by
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, WeierstrassDilatation.refinement_x, map_mul,
      AlgHom.commutes, dividedToXOpen, dividedOverlapMap_x, fromDivided_x]
    exact incidence_inverse W s π b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (xOpenUnit W s π b3 b4 b6) (xOpenUnit_val W s π b3 b4 b6).symm
  · simp only [AlgHom.comp_apply, WeierstrassDilatation.refinement_y, map_mul,
      AlgHom.commutes, dividedToXOpen, dividedOverlapMap_y, fromDivided_y]
    rw [← mul_assoc, incidence_inverse W s π b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (xOpenUnit W s π b3 b4 b6) (xOpenUnit_val W s π b3 b4 b6).symm]

/-- Both contractions agree on the actual common principal open. -/
@[reassoc] theorem overlapIso_toPrevious :
    (overlapIso W s π b3 b4 b6).hom ≫ dividedOpenInclusion W s π b3 b4 b6 ≫
        dividedToPrevious W s π b3 b4 b6 =
      xOpenInclusion W s π b3 b4 b6 ≫ toDivided W s π b3 b4 b6 := by
  have he : (overlapForward W s π b3 b4 b6).comp
      ((IsScalarTower.toAlgHom R _ (DividedOpen W s π b3 b4 b6)).comp
        (WeierstrassDilatation.refinement W s π
          (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl)) =
      (IsScalarTower.toAlgHom R _ (XOpen W s π b3 b4 b6)).comp
        (fromDivided W s π b3 b4 b6) := by
    apply AlgHom.ext
    intro z
    change overlapForward W s π b3 b4 b6 (algebraMap _ _
      (WeierstrassDilatation.refinement W s π
        (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl z)) = _
    rw [overlapForward_base]
    exact AlgHom.congr_fun (dividedToXOpen_refinement W s π b3 b4 b6) z
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun f : B →ₐ[R] XOpen W s π b3 b4 b6 =>
    CommRingCat.ofHom f.toRingHom) he)

end FLT.Mazur.WeierstrassSuccessiveX
