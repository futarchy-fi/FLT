/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberUnitScaling
public import FLT.Mazur.NodalFiberCoefficientRingMap
public import FLT.Mazur.PolygonSmoothingRingMap

/-!
# Full unit normalization commutes with coefficient maps

Compatible unit factors give commuting squares on both complete node rings,
including the nonreduced origins and both coordinate orientations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (c t : R) (d s : S) (u : Rˣ) (v : Sˣ)
  (hc : c = t * ↑u) (hd : d = s * ↑v)
  (hcd : f c = d) (hts : f t = s) (huv : f (u : R) = (v : S))
local notation "e" => unitSmoothingEquiv c t u hc
local notation "e'" => unitSmoothingEquiv d s v hd
local notation "N" => coefficientRingMap f c d hcd
local notation "P" => PolygonSmoothing.ringMap f t s hts

include huv in
/-- Forward unit normalization preserves the complete original coefficient map. -/
theorem unitSmoothingEquiv_coefficients :
    (P).comp (e).toAlgHom.toRingHom = (e').toAlgHom.toRingHom.comp N := by
  apply coefficient_ringHom_ext c
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toAlgHom, AlgEquiv.commutes, PolygonSmoothing.ringMap_scalar,
      coefficientRingMap_algebraMap]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toAlgHom, unitSmoothingEquiv_p, map_mul,
      PolygonSmoothing.ringMap_scalar, PolygonSmoothing.ringMap_left,
      coefficientRingMap_p, huv]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toAlgHom, unitSmoothingEquiv_q,
      PolygonSmoothing.ringMap_right, coefficientRingMap_q]

include huv in
/-- The inverse full chart comparison follows the same coefficient substitution. -/
theorem unitSmoothingEquiv_symm_coefficients :
    (N).comp (e).symm.toAlgHom.toRingHom = (e').symm.toAlgHom.toRingHom.comp P := by
  apply RingHom.ext
  intro z
  change N ((e).symm z) = (e').symm (P z)
  have h := DFunLike.congr_fun
    (unitSmoothingEquiv_coefficients f c t d s u v hc hd hcd hts huv) ((e).symm z)
  change P (e ((e).symm z)) = e' (N ((e).symm z)) at h
  simpa only [AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply] using
    (congrArg (e').symm h).symm

end FLT.Mazur.NodalFiber
