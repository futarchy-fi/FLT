/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXHorizontalLocalization
public import FLT.Mazur.WeierstrassSuccessiveXGluing

/-!
# Retaining the preceding horizontal open inside the local modification

The unchanged principal open of the preceding divided chart embeds as an
actual open subscheme of the glued local step. Its contraction is the original
principal-open inclusion, so it carries the same original functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)

/-- The actual retained-horizontal open of the successive x-direction chart. -/
def horizontalOpenInclusion : Spec (.of (HorizontalOpen W s π b3 b4 b6)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A _))

/-- The actual horizontal principal open of the preceding divided chart. -/
def previousHorizontalInclusion : Spec (.of (PreviousHorizontalOpen W s π b3 b4 b6)) ⟶
    Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B _))

instance horizontalOpenInclusion_isOpenImmersion :
    IsOpenImmersion (horizontalOpenInclusion W s π b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (coord W s π b3 b4 b6 2)

instance previousHorizontalInclusion_isOpenImmersion :
    IsOpenImmersion (previousHorizontalInclusion W s π b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization
    (WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6))

/-- The actual scheme isomorphism induced by the horizontal fraction comparison. -/
def horizontalIso : Spec (.of (HorizontalOpen W s π b3 b4 b6)) ≅
    Spec (.of (PreviousHorizontalOpen W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso (horizontalEquiv W s π b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The horizontal comparison is over the preceding divided chart. -/
@[reassoc] theorem horizontalIso_toDivided :
    (horizontalIso W s π b3 b4 b6).hom ≫ previousHorizontalInclusion W s π b3 b4 b6 =
      horizontalOpenInclusion W s π b3 b4 b6 ≫ toDivided W s π b3 b4 b6 := by
  have he : (horizontalForward W s π b3 b4 b6).comp
      (IsScalarTower.toAlgHom R B _) =
      (IsScalarTower.toAlgHom R A _).comp (fromDivided W s π b3 b4 b6) := by
    apply AlgHom.ext
    intro z
    exact horizontalForward_base W s π b3 b4 b6 z
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun f : B →ₐ[R] HorizontalOpen W s π b3 b4 b6 =>
    CommRingCat.ofHom f.toRingHom) he)

/-- The same preceding horizontal open embeds in the glued successive modification. -/
def previousHorizontalChart : Spec (.of (PreviousHorizontalOpen W s π b3 b4 b6)) ⟶
    modification W s π b3 b4 b6 :=
  (horizontalIso W s π b3 b4 b6).inv ≫ horizontalOpenInclusion W s π b3 b4 b6 ≫
    xChart W s π b3 b4 b6

instance previousHorizontalChart_isOpenImmersion :
    IsOpenImmersion (previousHorizontalChart W s π b3 b4 b6) := by
  unfold previousHorizontalChart
  infer_instance

/-- The retained open contracts by its original inclusion, with no change of functions. -/
@[reassoc] theorem previousHorizontalChart_contraction :
    previousHorizontalChart W s π b3 b4 b6 ≫ contraction W s π b3 b4 b6 =
      previousHorizontalInclusion W s π b3 b4 b6 := by
  simp only [previousHorizontalChart, Category.assoc, xChart_contraction]
  rw [← horizontalIso_toDivided, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassSuccessiveX
