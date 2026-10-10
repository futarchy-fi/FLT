/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicBoundaryParameters
public import FLT.Mazur.WeierstrassModificationXConicOverlapParameterMaps

/-!
# The incidence boundary is the entire ordered parameter overlap

For unit divided constant the original t-localization and the original
double tangent localization are isomorphic, retaining all conic functions
and both ordered parameters.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R)
local notation "C₀" => ConicCoordinate a c
local notation "O₁" => ConicFirstOpen a c
local notation "B" => ConicIncidenceOpen a c
local notation "Q" => ConicParameterOverlap a c
local notation "g" => IsScalarTower.toAlgHom R C₀ Q

/-- Incidence is invertible on the full intersection of the two tangent opens. -/
theorem conicOverlap_incidence_isUnit : IsUnit (g (conicT a c)) := by
  have hr : g (conicV a c) * g (conicV a c + algebraMap R C₀ a) =
      algebraMap R Q c * g (conicT a c) ^ 2 := by
    have h := congrArg g (conic_relation a c)
    simpa only [map_sub, map_mul, map_pow, map_zero, AlgHom.commutes,
      sub_eq_zero] using h
  have h := (conicOverlap_second_isUnit a c).mul (conicOverlap_first_isUnit a c)
  rw [hr, pow_two] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)

/-- Restrict incidence functions to the actual double tangent overlap. -/
def conicIncidenceToOverlap : B →ₐ[R] Q :=
  IsLocalization.Away.liftAlgHom (f := g) (conicT a c) (conicOverlap_incidence_isUnit a c)

/-- This restriction retains all original conic functions. -/
theorem conicIncidenceToOverlap_base (q : C₀) :
    conicIncidenceToOverlap a c (algebraMap C₀ B q) = g q := by
  rw [conicIncidenceToOverlap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- Extend both tangent localizations to the entire incidence boundary. -/
def conicOverlapToIncidence (hc : IsUnit c) : Q →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := conicFirstToIncidence a c hc)
    (algebraMap C₀ O₁ (conicV a c)) (by
      rw [conicFirstToIncidence_base]
      exact (conicIncidence_tangent_units a c hc).1)

/-- The extension retains the entire first tangent chart. -/
theorem conicOverlapToIncidence_first (hc : IsUnit c) (q : O₁) :
    conicOverlapToIncidence a c hc (algebraMap O₁ Q q) = conicFirstToIncidence a c hc q := by
  rw [conicOverlapToIncidence, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The extension retains every original conic function. -/
theorem conicOverlapToIncidence_base (hc : IsUnit c) (q : C₀) :
    conicOverlapToIncidence a c hc (g q) = algebraMap C₀ B q := by
  change conicOverlapToIncidence a c hc (algebraMap O₁ Q (algebraMap C₀ O₁ q)) = _
  rw [conicOverlapToIncidence_first, conicFirstToIncidence_base]

/-- Restriction and extension are inverse on the entire incidence algebra. -/
theorem conicOverlapToIncidence_comp (hc : IsUnit c) :
    (conicOverlapToIncidence a c hc).comp (conicIncidenceToOverlap a c) =
      AlgHom.id R B := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicT a c))
  apply AlgHom.ext
  intro q
  change conicOverlapToIncidence a c hc
    (conicIncidenceToOverlap a c (algebraMap C₀ B q)) = algebraMap C₀ B q
  rw [conicIncidenceToOverlap_base, conicOverlapToIncidence_base]

/-- Restriction and extension are inverse on the full double localization. -/
theorem conicIncidenceToOverlap_comp (hc : IsUnit c) :
    (conicIncidenceToOverlap a c).comp (conicOverlapToIncidence a c hc) =
      AlgHom.id R Q := by
  apply IsLocalization.algHom_ext (Submonoid.powers (algebraMap C₀ O₁ (conicV a c)))
  apply IsLocalization.algHom_ext
    (Submonoid.powers (conicV a c + algebraMap R C₀ a))
  apply AlgHom.ext
  intro q
  change conicIncidenceToOverlap a c
    (conicOverlapToIncidence a c hc (g q)) = g q
  rw [conicOverlapToIncidence_base, conicIncidenceToOverlap_base]

/-- The original incidence localization is exactly the full ordered overlap. -/
def conicIncidenceOverlapEquiv (hc : IsUnit c) : B ≃ₐ[R] Q :=
  AlgEquiv.ofAlgHom (conicIncidenceToOverlap a c) (conicOverlapToIncidence a c hc)
    (conicIncidenceToOverlap_comp a c hc) (conicOverlapToIncidence_comp a c hc)

/-- The comparison preserves the first original ratio. -/
theorem conicOverlapToIncidence_firstParameter (hc : IsUnit c) :
    conicOverlapToIncidence a c hc (conicOverlapFirstParameter a c) =
      conicIncidenceFirstParameter a c hc :=
  conicOverlapToIncidence_first a c hc _

/-- The comparison preserves the second original ratio, with its orientation. -/
theorem conicOverlapToIncidence_secondParameter (hc : IsUnit c) :
    conicOverlapToIncidence a c hc (conicOverlapSecondParameter a c) =
      conicIncidenceSecondParameter a c hc := by
  apply (conicIncidence_tangent_units a c hc).1.mul_right_cancel
  rw [conicIncidenceSecondParameter_mul]
  have h := congrArg (conicOverlapToIncidence a c hc)
    (conicOverlapSecondParameter_mul a c)
  simpa only [map_mul, conicOverlapToIncidence_base] using h

end FLT.Mazur.WeierstrassModificationX
