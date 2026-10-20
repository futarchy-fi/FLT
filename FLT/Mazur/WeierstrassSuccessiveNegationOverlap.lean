/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LocalizationFixedInvolution
public import FLT.Mazur.WeierstrassSuccessiveXNegationContraction
public import FLT.Mazur.WeierstrassSuccessiveXGluing

/-!
# Negation on the actual successive gluing overlap

Extend the incidence negative to the principal open where incidence is a unit.
Its original divided coordinate substitution commutes with divided negation,
so the two full chart involutions agree on the actual scheme overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "L" => XOpen W s π b3 b4 b6
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "t" => coord W s π b3 b4 b6 0
local notation "f" => negation W s π b3 b4 b6
local notation "nf" => LocalizationFixedInvolution.lift f t (negation_t W s π b3 b4 b6)
local notation "z" => xOpenUnit W s π b3 b4 b6

/-- Negation fixes the actual inverse incidence function as well as incidence. -/
theorem openNegation_inverse : nf (↑(z)⁻¹ : L) = (↑(z)⁻¹ : L) := by
  have hu : Units.map (nf).toMonoidHom z = z := by
    apply Units.ext
    change nf (↑z : L) = (↑z : L)
    rw [xOpenUnit_val, LocalizationFixedInvolution.lift_base, negation_t]
  exact congrArg (fun q : Lˣ => (↑q⁻¹ : L)) hu

/-- Negation commutes with the full divided substitution on the actual overlap. -/
theorem openNegation_dividedToXOpen :
    (nf).comp (dividedToXOpen W s π b3 b4 b6) =
      (dividedToXOpen W s π b3 b4 b6).comp
        (WeierstrassDilatation.negation W (s * π) b3 b4 b6) := by
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, dividedToXOpen, dividedOverlapMap_x,
      WeierstrassDilatation.negation_x, openNegation_inverse]
  · simp only [AlgHom.comp_apply, dividedToXOpen, dividedOverlapMap_y,
      WeierstrassDilatation.negation_y, map_sub, map_neg, map_mul, AlgHom.commutes,
      dividedOverlapMap_x, openNegation_inverse]
    change (↑(z)⁻¹ : L) * nf (algebraMap A L (coord W s π b3 b4 b6 1)) = _
    rw [LocalizationFixedInvolution.lift_base, negation_v]
    simp only [map_sub, map_neg, map_mul, IsScalarTower.algebraMap_apply R A L,
      IsScalarTower.toAlgHom_apply]
    rw [← xOpenUnit_val]
    linear_combination -algebraMap R L b3 * Units.inv_mul z

/-- The overlap negative is defined on the entire actual principal open. -/
def openNegationIso : Spec (.of L) ≅ Spec (.of L) :=
  LocalizationFixedInvolution.specIso f t (negation_t W s π b3 b4 b6)
    (negation_comp W s π b3 b4 b6)

/-- The overlap negative retains its incidence-chart embedding. -/
@[reassoc] theorem openNegationIso_inclusion :
    (openNegationIso W s π b3 b4 b6).hom ≫ xOpenInclusion W s π b3 b4 b6 =
      xOpenInclusion W s π b3 b4 b6 ≫ (negationIso W s π b3 b4 b6).hom :=
  LocalizationFixedInvolution.specIso_inclusion f t (negation_t W s π b3 b4 b6)
    (negation_comp W s π b3 b4 b6)

/-- The actual overlap morphism is the constructed divided coordinate substitution. -/
theorem overlapToDivided_eq_spec : overlapToDivided W s π b3 b4 b6 =
    Spec.map (CommRingCat.ofHom (dividedToXOpen W s π b3 b4 b6).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact overlapForward_base W s π b3 b4 b6 a

/-- The overlap negative retains the original divided-chart embedding. -/
@[reassoc] theorem openNegationIso_toDivided :
    (openNegationIso W s π b3 b4 b6).hom ≫ overlapToDivided W s π b3 b4 b6 =
      overlapToDivided W s π b3 b4 b6 ≫
        (WeierstrassDilatation.negationIso W (s * π) b3 b4 b6).hom := by
  rw [overlapToDivided_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun g : D →ₐ[R] L => CommRingCat.ofHom g.toRingHom)
    (openNegation_dividedToXOpen W s π b3 b4 b6))

/-- Both complete chart negatives agree along the exact gluing overlap. -/
theorem negation_chart_overlap :
    xOpenInclusion W s π b3 b4 b6 ≫
        (negationIso W s π b3 b4 b6).hom ≫ xChart W s π b3 b4 b6 =
      overlapToDivided W s π b3 b4 b6 ≫
        (WeierstrassDilatation.negationIso W (s * π) b3 b4 b6).hom ≫
          dividedChart W s π b3 b4 b6 := by
  rw [← openNegationIso_inclusion_assoc, chart_overlap,
    openNegationIso_toDivided_assoc]

end FLT.Mazur.WeierstrassSuccessiveX
