/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicFirstInverse
public import FLT.Mazur.WeierstrassModificationXConicTangentSwitch

/-!
# The actual second tangent neighborhood of the conic

Recentering w=v+a identifies the original v-invertible neighborhood with the
first tangent neighborhood for -a. Both localization maps and their inverse
identities are constructed from the conic coordinate translations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)

/-- The second neighborhood inverts the original slope v. -/
abbrev ConicSecondOpen := Localization.Away (conicV a c)
local notation "C₀" => ConicCoordinate a c
local notation "C₁" => ConicCoordinate (-a) c
local notation "O₀" => ConicSecondOpen a c
local notation "O₁" => ConicFirstOpen (-a) c

/-- Recentering defines a map from the actual second open to the first for -a. -/
def conicSecondToFirst : O₀ →ₐ[R] O₁ :=
  IsLocalization.Away.liftAlgHom
    (f := (Algebra.algHom R C₁ O₁).comp (conicTangentEquiv a c).toAlgHom)
    (conicV a c) (by
      change IsUnit (algebraMap C₁ O₁ (conicTangentEquiv a c (conicV a c)))
      rw [conicTangentEquiv_v]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- The reverse translation defines the inverse localization map. -/
def conicFirstToSecond : O₁ →ₐ[R] O₀ :=
  IsLocalization.Away.liftAlgHom
    (f := (Algebra.algHom R C₀ O₀).comp (conicTangentEquiv a c).symm.toAlgHom)
    (conicV (-a) c + algebraMap R C₁ (-a)) (by
      change IsUnit (algebraMap C₀ O₀
        ((conicTangentEquiv a c).symm (conicV (-a) c + algebraMap R C₁ (-a))))
      rw [← conicTangentEquiv_v, AlgEquiv.symm_apply_apply]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- The first map is the original translation on every conic function. -/
theorem conicSecondToFirst_base (q : C₀) :
    conicSecondToFirst a c (algebraMap C₀ O₀ q) =
    algebraMap C₁ O₁ (conicTangentEquiv a c q) := by
  rw [conicSecondToFirst, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The reverse map is the inverse translation on every conic function. -/
theorem conicFirstToSecond_base (q : C₁) :
    conicFirstToSecond a c (algebraMap C₁ O₁ q) =
    algebraMap C₀ O₀ ((conicTangentEquiv a c).symm q) := by
  rw [conicFirstToSecond, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The localized translations are inverse on the original second open. -/
theorem conicFirstToSecond_comp :
    (conicFirstToSecond a c).comp (conicSecondToFirst a c) = AlgHom.id R O₀ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicV a c))
  apply AlgHom.ext
  intro q
  change conicFirstToSecond a c (conicSecondToFirst a c (algebraMap C₀ O₀ q)) = _
  rw [conicSecondToFirst_base, conicFirstToSecond_base, AlgEquiv.symm_apply_apply]
  rfl

/-- The localized translations are inverse on the recentered first open. -/
theorem conicSecondToFirst_comp :
    (conicSecondToFirst a c).comp (conicFirstToSecond a c) = AlgHom.id R O₁ := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (conicV (-a) c + algebraMap R C₁ (-a)))
  apply AlgHom.ext
  intro q
  change conicSecondToFirst a c (conicFirstToSecond a c (algebraMap C₁ O₁ q)) = _
  rw [conicFirstToSecond_base, conicSecondToFirst_base, AlgEquiv.apply_symm_apply]
  rfl

/-- The two actual oriented neighborhoods are isomorphic after recentering. -/
def conicSecondOpenEquiv : O₀ ≃ₐ[R] O₁ :=
  AlgEquiv.ofAlgHom (conicSecondToFirst a c) (conicFirstToSecond a c)
    (conicSecondToFirst_comp a c) (conicFirstToSecond_comp a c)

/-- The original second open is a rational parameter open with coefficient c retained. -/
def conicSecondParameterEquiv (ha : IsUnit a) : ConicParameterOpen c ≃ₐ[R] O₀ :=
  (conicFirstParameterEquiv (-a) c ha.neg).trans (conicSecondOpenEquiv a c).symm

end FLT.Mazur.WeierstrassModificationX
