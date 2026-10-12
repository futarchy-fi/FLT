/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXShearLocalization
public import FLT.Mazur.WeierstrassSuccessiveXShearContraction
public import FLT.Mazur.WeierstrassSuccessiveXGluing

/-!
# Shearing the complete successive local modification

Both original charts and their actual reciprocal attachment are retained.
The glued isomorphism commutes with contraction to the preceding divided chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "i" => xOpenInclusion W s π b3 b4 b6
local notation "i'" => xOpenInclusion U s π b3 (b4 - r * b3) b6
local notation "j" => overlapToDivided W s π b3 b4 b6
local notation "j'" => overlapToDivided U s π b3 (b4 - r * b3) b6

/-- The complete successive incidence chart shear. -/
def shearChartIso : Spec (.of (Coordinate U s π b3 (b4 - r * b3) b6)) ≅
    Spec (.of (Coordinate W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso (shearEquiv W s π b3 b4 b6 r).toRingEquiv.toCommRingCatIso.op

/-- The complete deeper divided chart shear. -/
def shearDividedIso :
    Spec (.of (WeierstrassDilatation.Coordinate U (s * π) b3 (b4 - r * b3) b6)) ≅
      Spec (.of (WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6)) :=
  Scheme.Spec.mapIso (WeierstrassDilatation.shearEquiv W (s * π) b3 b4 b6 r
    ).toRingEquiv.toCommRingCatIso.op

/-- The complete successive reciprocal overlap shear. -/
def shearOverlapIso : Spec (.of (XOpen U s π b3 (b4 - r * b3) b6)) ≅
    Spec (.of (XOpen W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso (xOpenShearEquiv W s π b3 b4 b6 r).toRingEquiv.toCommRingCatIso.op

/-- The localized shear retains the actual incidence inclusion. -/
@[reassoc] theorem shearOverlapIso_incidence :
    i' ≫ (shearChartIso W s π b3 b4 b6 r).hom =
      (shearOverlapIso W s π b3 b4 b6 r).hom ≫ i := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (xOpenShearEquiv_base W s π b3 b4 b6 r z).symm

/-- The original divided attachment is its full algebra substitution. -/
theorem shear_overlapToDivided_spec :
    j = Spec.map (CommRingCat.ofHom (dividedToXOpen W s π b3 b4 b6).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact overlapForward_base W s π b3 b4 b6 z

/-- The localized shear retains the actual deeper divided attachment. -/
@[reassoc] theorem shearOverlapIso_divided :
    j' ≫ (shearDividedIso W s π b3 b4 b6 r).hom =
      (shearOverlapIso W s π b3 b4 b6 r).hom ≫ j := by
  rw [shear_overlapToDivided_spec, shear_overlapToDivided_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (xOpenShearEquiv_dividedToXOpen W s π b3 b4 b6 r).symm

/-- The actual two-chart successive modification is preserved by shear. -/
def shearModificationIso : modification U s π b3 (b4 - r * b3) b6 ≅
    modification W s π b3 b4 b6 :=
  asIso (pushout.map i' j' i j (shearChartIso W s π b3 b4 b6 r).hom
    (shearDividedIso W s π b3 b4 b6 r).hom (shearOverlapIso W s π b3 b4 b6 r).hom
    (shearOverlapIso_incidence W s π b3 b4 b6 r) (shearOverlapIso_divided W s π b3 b4 b6 r))

/-- The whole comparison retains every successive incidence function. -/
@[reassoc] theorem shearModificationIso_incidence :
    xChart U s π b3 (b4 - r * b3) b6 ≫ (shearModificationIso W s π b3 b4 b6 r).hom =
      (shearChartIso W s π b3 b4 b6 r).hom ≫ xChart W s π b3 b4 b6 := by
  simp [shearModificationIso, xChart]

/-- The whole comparison retains every deeper divided function. -/
@[reassoc] theorem shearModificationIso_divided :
    dividedChart U s π b3 (b4 - r * b3) b6 ≫ (shearModificationIso W s π b3 b4 b6 r).hom =
      (shearDividedIso W s π b3 b4 b6 r).hom ≫ dividedChart W s π b3 b4 b6 := by
  simp [shearModificationIso, dividedChart]

/-- The deeper refinement commutes with the parameter-corrected preceding shear. -/
@[reassoc] theorem shearDividedIso_toPrevious :
    (shearDividedIso W s π b3 b4 b6 r).hom ≫ dividedToPrevious W s π b3 b4 b6 =
      dividedToPrevious U s π b3 (b4 - r * b3) b6 ≫
        Spec.map (CommRingCat.ofHom (precedingShearEquiv W s π b3 b4 b6 r).toRingHom) := by
  have h : (WeierstrassDilatation.shearForward W (s * π) b3 b4 b6 r).comp
      (WeierstrassDilatation.refinement W s π
        (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl) =
      (WeierstrassDilatation.refinement U s π (π * b3) (π * (b4 - r * b3))
        (π ^ 2 * b6) b3 (b4 - r * b3) b6 rfl rfl rfl).comp
          (precedingShearEquiv W s π b3 b4 b6 r).toAlgHom := by
    apply WeierstrassDilatation.hom_ext
    · simp [precedingShearEquiv_x]
    · simp [precedingShearEquiv_y, mul_add, mul_left_comm]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) h

/-- The full successive modification comparison retains its original contraction. -/
@[reassoc] theorem shearModificationIso_contraction :
    (shearModificationIso W s π b3 b4 b6 r).hom ≫ contraction W s π b3 b4 b6 =
      contraction U s π b3 (b4 - r * b3) b6 ≫
        Spec.map (CommRingCat.ofHom (precedingShearEquiv W s π b3 b4 b6 r).toRingHom) := by
  apply pushout.hom_ext
  · change xChart U s π b3 (b4 - r * b3) b6 ≫ _ =
      xChart U s π b3 (b4 - r * b3) b6 ≫ _
    rw [shearModificationIso_incidence_assoc, xChart_contraction, xChart_contraction_assoc]
    exact shearSpec_toDivided W s π b3 b4 b6 r
  · change dividedChart U s π b3 (b4 - r * b3) b6 ≫ _ =
      dividedChart U s π b3 (b4 - r * b3) b6 ≫ _
    rw [shearModificationIso_divided_assoc, dividedChart_contraction,
      dividedChart_contraction_assoc]
    exact shearDividedIso_toPrevious W s π b3 b4 b6 r

end FLT.Mazur.WeierstrassSuccessiveX
