/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYOverlap
public import FLT.Mazur.WeierstrassModificationXLocalization

/-!
# The y-chart substitution factors through the x/divided overlap

Over any test algebra where both y-chart ratios are units, the incidence
coordinate r/u is a unit. The resulting map from the actual x-direction
localization recovers the divided-chart substitution on every function.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (a b : Sˣ) (ha : f (coord W s b3 b4 b6 0) = a)
  (hb : f (coord W s b3 b4 b6 1) = b)

include ha in
/-- Inverting both ratios makes the x-chart incidence coordinate invertible. -/
theorem toX_t_isUnit :
    IsUnit (toX W s b3 b4 b6 f b hb (WeierstrassModificationX.t W s b3 b4 b6)) := by
  rw [toX_t, ha]
  exact a.isUnit.mul b⁻¹.isUnit

/-- The actual factorization through the x/divided principal-open algebra. -/
def toXOpen : WeierstrassModificationX.XOpen W s b3 b4 b6 →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (WeierstrassModificationX.t W s b3 b4 b6)
    (f := toX W s b3 b4 b6 f b hb) (toX_t_isUnit W s b3 b4 b6 f a b ha hb)

/-- The factorization restricts to the prescribed x-chart map. -/
@[simp] theorem toXOpen_base (z : WeierstrassModificationX.Coordinate W s b3 b4 b6) :
    toXOpen W s b3 b4 b6 f a b ha hb (algebraMap _ _ z) =
      toX W s b3 b4 b6 f b hb z := by
  rw [toXOpen, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The localized incidence inverse is u/r under the triple-overlap map. -/
theorem toXOpen_inverse :
    toXOpen W s b3 b4 b6 f a b ha hb (↑(WeierstrassModificationX.xOpenUnit
      W s b3 b4 b6)⁻¹) = (↑b : S) * (↑a⁻¹ : S) := by
  have h := WeierstrassModificationX.map_inverse_unit
    (toXOpen W s b3 b4 b6 f a b ha hb).toRingHom
    (WeierstrassModificationX.xOpenUnit W s b3 b4 b6) (b * a⁻¹) (by
      change toXOpen W s b3 b4 b6 f a b ha hb
        (↑(WeierstrassModificationX.xOpenUnit W s b3 b4 b6)) = _
      rw [WeierstrassModificationX.xOpenUnit_val, toXOpen_base, toX_t, ha]
      simp only [mul_inv_rev, inv_inv, Units.val_mul])
  exact h

/-- Both routes from the divided chart coincide on the common principal open. -/
theorem toXOpen_dividedToXOpen :
    (toXOpen W s b3 b4 b6 f a b ha hb).comp
        (WeierstrassModificationX.dividedToXOpen W s b3 b4 b6) =
      toDivided W s b3 b4 b6 f a ha := by
  apply WeierstrassDilatation.hom_ext
  · change toXOpen W s b3 b4 b6 f a b ha hb
      (WeierstrassModificationX.dividedOverlapMap W s b3 b4 b6
        (IsScalarTower.toAlgHom R _ _) (WeierstrassModificationX.xOpenUnit W s b3 b4 b6)
        (WeierstrassModificationX.xOpenUnit_val W s b3 b4 b6).symm
        (WeierstrassDilatation.x W s b3 b4 b6)) = _
    rw [WeierstrassModificationX.dividedOverlapMap_x, toXOpen_inverse, toDivided_x, hb]
  · change toXOpen W s b3 b4 b6 f a b ha hb
      (WeierstrassModificationX.dividedOverlapMap W s b3 b4 b6
        (IsScalarTower.toAlgHom R _ _) (WeierstrassModificationX.xOpenUnit W s b3 b4 b6)
        (WeierstrassModificationX.xOpenUnit_val W s b3 b4 b6).symm
        (WeierstrassDilatation.y W s b3 b4 b6)) = _
    rw [WeierstrassModificationX.dividedOverlapMap_y, map_mul, toXOpen_inverse]
    change (↑b : S) * (↑a⁻¹ : S) * toXOpen W s b3 b4 b6 f a b ha hb
      (algebraMap _ _ (WeierstrassModificationX.v W s b3 b4 b6)) = _
    rw [toXOpen_base, toX_v, toDivided_y, mul_right_comm, Units.mul_inv, one_mul]

/-- The x-chart substitution commutes with arbitrary algebra maps. -/
theorem toX_naturality {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T) :
    g.comp (toX W s b3 b4 b6 f b hb) =
      toX W s b3 b4 b6 (g.comp f) (b.map g.toMonoidHom)
        (congrArg g hb) := by
  apply WeierstrassModificationX.hom_ext
  · simp only [AlgHom.comp_apply, toX_t, map_mul, Units.coe_map_inv]
    rfl
  · simp only [AlgHom.comp_apply, toX_v, Units.coe_map_inv]
    rfl

/-- The divided-chart substitution commutes with arbitrary algebra maps. -/
theorem toDivided_naturality {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T) :
    g.comp (toDivided W s b3 b4 b6 f a ha) =
      toDivided W s b3 b4 b6 (g.comp f) (a.map g.toMonoidHom)
        (congrArg g ha) := by
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, toDivided_x, map_mul, Units.coe_map_inv]
    rfl
  · simp only [AlgHom.comp_apply, toDivided_y, Units.coe_map_inv]
    rfl

end FLT.Mazur.WeierstrassModificationY
