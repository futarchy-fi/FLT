/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentMobiusBoundary
public import FLT.Mazur.NodalFiberTangentMobiusNaturality
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Arithmetic coefficient squares for the entire fractional polygon chart

The original tangent-open restriction and the polygon coefficient restriction
commute on the whole chart. Both smoothing parameters remain explicitly named.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (s t : R) (a : Rˣ) (hs : s = (a : R) ^ 2 * t)
  (s' t' : S) (hs' : f s = s') (ht' : f t = t')
local notation "a'" => Units.map f.toMonoidHom a
local notation "h'" => tangentMobius_smoothing_map f s t a hs s' t' hs' ht'
local notation "C" => tangentCoefficientRingMap f s (a : R) s' (a' : S) hs' rfl
local notation "P" => PolygonSmoothing.ringMap f t t' ht'

/-- Every polygon function follows the original arithmetic restriction through the full chart. -/
theorem tangentMobiusEvaluation_coefficients :
    (C).comp (tangentMobiusEvaluation s t a hs).toRingHom =
      (tangentMobiusEvaluation s' t' a' h').toRingHom.comp P := by
  apply PolygonSmoothing.chartRing_ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, tangentCoefficientRingMap_scalar, PolygonSmoothing.ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      tangentMobiusEvaluation_left, map_add, map_mul, tangentCoefficientRingMap_scalar,
      tangentCoefficientRingMap_p, PolygonSmoothing.ringMap_left]
    rw [ht']
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      tangentMobiusEvaluation_right, tangentCoefficientRingMap_fraction,
      PolygonSmoothing.ringMap_right]

/-- The original arithmetic coefficient square holds as an equality of full scheme morphisms. -/
@[reassoc] theorem tangentMobiusChart_coefficients :
    Spec.map (CommRingCat.ofHom C) ≫ tangentMobiusChart s t a hs =
      tangentMobiusChart s' t' a' h' ≫ Spec.map (CommRingCat.ofHom P) := by
  rw [tangentMobiusChart_eq_spec, tangentMobiusChart_eq_spec,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact tangentMobiusEvaluation_coefficients f s t a hs s' t' hs' ht'

end FLT.Mazur.NodalFiber
