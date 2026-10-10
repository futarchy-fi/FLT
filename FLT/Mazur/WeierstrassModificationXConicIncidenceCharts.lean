/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicParameterOrigin
public import FLT.Mazur.WeierstrassModificationXConicSecondCoordinates

/-!
# Scheme-theoretic incidence sections in the two conic charts

In each original tangent neighborhood the incidence equation t=0 becomes
exactly z=0. The quotient is R, and the two original slopes are 0 and -a.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "P" => ConicParameterOpen c
local notation "C₀" => ConicCoordinate a c
local notation "O₀" => ConicFirstOpen a c
local notation "O₁" => ConicSecondOpen a c

include ha in
/-- The inverse incidence formula generates exactly the parameter-origin ideal. -/
theorem conicInverseT_span : Ideal.span {conicInverseT a c} = conicParameterOriginIdeal c := by
  rw [conicInverseT, Ideal.span_singleton_mul_right_unit (conicParameterInv_isUnit c),
    Ideal.span_singleton_mul_left_unit (ha.map (algebraMap R P))]
  rfl

/-- The first chart identifies the original incidence ideal with the parameter origin. -/
theorem conicFirstParameterEquiv_incidence :
    Ideal.map (conicFirstParameterEquiv a c ha).symm.toRingHom
      (Ideal.span {algebraMap C₀ O₀ (conicT a c)}) = conicParameterOriginIdeal c := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {conicFirstToParameter a c ha (algebraMap C₀ O₀ (conicT a c))} = _
  rw [conicFirstToParameter_base, conicToParameter_t, conicInverseT_span a c ha]

/-- The second chart identifies the original incidence ideal with the parameter origin. -/
theorem conicSecondParameterEquiv_incidence :
    Ideal.map (conicSecondParameterEquiv a c ha).symm.toRingHom
      (Ideal.span {algebraMap C₀ O₁ (conicT a c)}) = conicParameterOriginIdeal c := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {((conicSecondParameterEquiv a c ha).symm
    (algebraMap C₀ O₁ (conicT a c)))} = _
  rw [conicSecondParameterEquiv_symm_t, conicInverseT_span (-a) c ha.neg]

/-- The original first incidence section has coordinate algebra R. -/
def conicFirstIncidenceEquiv :
    (O₀ ⧸ Ideal.span {algebraMap C₀ O₀ (conicT a c)}) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlg _ _ (conicFirstParameterEquiv a c ha).symm
    (conicFirstParameterEquiv_incidence a c ha).symm).trans (conicParameterOriginEquiv c)

/-- The original second incidence section has coordinate algebra R. -/
def conicSecondIncidenceEquiv :
    (O₁ ⧸ Ideal.span {algebraMap C₀ O₁ (conicT a c)}) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlg _ _ (conicSecondParameterEquiv a c ha).symm
    (conicSecondParameterEquiv_incidence a c ha).symm).trans (conicParameterOriginEquiv c)

/-- The first section equivalence is evaluation through the actual inverse chart. -/
theorem conicFirstIncidenceEquiv_mk (q : O₀) :
    conicFirstIncidenceEquiv a c ha (Ideal.Quotient.mk _ q) =
      conicParameterOrigin c ((conicFirstParameterEquiv a c ha).symm q) := by
  rw [conicFirstIncidenceEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk,
    conicParameterOriginEquiv_mk]

/-- The second section equivalence is evaluation through the actual inverse chart. -/
theorem conicSecondIncidenceEquiv_mk (q : O₁) :
    conicSecondIncidenceEquiv a c ha (Ideal.Quotient.mk _ q) =
      conicParameterOrigin c ((conicSecondParameterEquiv a c ha).symm q) := by
  rw [conicSecondIncidenceEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk,
    conicParameterOriginEquiv_mk]

/-- The first scheme-theoretic incidence section retains original slope zero. -/
theorem conicFirstIncidenceEquiv_v : conicFirstIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap C₀ O₀ (conicV a c))) = 0 := by
  rw [conicFirstIncidenceEquiv_mk]
  change conicParameterOrigin c (conicFirstToParameter a c ha _) = 0
  rw [conicFirstToParameter_base, conicToParameter_v, conicParameterOrigin_inverseV]

/-- The second scheme-theoretic incidence section retains original slope -a. -/
theorem conicSecondIncidenceEquiv_v : conicSecondIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap C₀ O₁ (conicV a c))) = -a := by
  rw [conicSecondIncidenceEquiv_mk, conicSecondParameterEquiv_symm_v,
    map_sub, conicParameterOrigin_inverseV, AlgHom.commutes, zero_sub]
  rfl

end FLT.Mazur.WeierstrassModificationX
