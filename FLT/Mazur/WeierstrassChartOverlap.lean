/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Coordinate maps between integral Weierstrass charts

Localize one chart at a second homogeneous coordinate and normalize by that
unit. The resulting map from the second chart extends to its overlap algebra.
These maps are integral and require no discriminant or smoothness assumption.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k : Fin 3)

/-- The principal open of chart j where coordinate k is invertible. -/
abbrev Overlap := Localization.Away (coord W j k)

/-- The chart coordinates restricted to the principal open. -/
def overlapCoord (i : Fin 3) : Overlap W j k :=
  algebraMap (Coordinate W j) (Overlap W j k) (coord W j i)

/-- The first chart remains normalized after localization. -/
@[simp] theorem overlapCoord_self : overlapCoord W j k j = 1 := by
  simp only [overlapCoord, coord_self, map_one]

/-- The second chart's normalizing coordinate is a unit on the overlap. -/
theorem overlapCoord_isUnit : IsUnit (overlapCoord W j k k) :=
  IsLocalization.Away.algebraMap_isUnit (coord W j k)

/-- Restricted coordinates still solve the cubic. -/
theorem overlapCoord_equation :
    (W.map (algebraMap R (Overlap W j k))).toProjective.Equation
      (overlapCoord W j k) := by
  change (W.map (algebraMap R (Overlap W j k))).toProjective.Equation
    (fun i => algebraMap (Coordinate W j) (Overlap W j k) (coord W j i))
  have h := (coord_equation W j).map (algebraMap (Coordinate W j) (Overlap W j k))
  simpa only [Function.comp_def, WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R
    (Coordinate W j) (Overlap W j k)] using h

/-- The inverse of the homogeneous coordinate used to change charts. -/
def overlapInverse : Overlap W j k := ↑(overlapCoord_isUnit W j k).unit⁻¹

/-- The overlap inverse cancels the second homogeneous coordinate. -/
@[simp] theorem overlapInverse_mul :
    overlapInverse W j k * overlapCoord W j k k = 1 :=
  Units.inv_mul_eq_one.mpr (overlapCoord_isUnit W j k).unit_spec

/-- The inverse coordinate is itself a unit. -/
theorem overlapInverse_isUnit : IsUnit (overlapInverse W j k) := Units.isUnit _

/-- The second chart evaluates at the integrally rescaled universal coordinates. -/
def transitionBase : Coordinate W k →ₐ[R] Overlap W j k :=
  evaluation W k (overlapInverse W j k • overlapCoord W j k)
    (((W.map (algebraMap R (Overlap W j k))).toProjective.equation_smul _
      (overlapInverse_isUnit W j k)).mpr (overlapCoord_equation W j k))
    (overlapInverse_mul W j k)

/-- Changing charts divides each coordinate by the new normalizing coordinate. -/
@[simp] theorem transitionBase_coord (i : Fin 3) :
    transitionBase W j k (coord W k i) = overlapInverse W j k * overlapCoord W j k i :=
  evaluation_coord W k _ _ _ i

/-- The coordinate inverted on the source overlap maps to a unit. -/
theorem transitionBase_isUnit : IsUnit (transitionBase W j k (coord W k j)) := by
  rw [transitionBase_coord, overlapCoord_self, mul_one]
  exact overlapInverse_isUnit W j k

/-- The integral transition map between the two principal overlap algebras. -/
def transition : Overlap W k j →ₐ[R] Overlap W j k :=
  IsLocalization.Away.liftAlgHom (coord W k j) (transitionBase_isUnit W j k)

/-- The transition map extends the explicit coordinate rescaling. -/
@[simp] theorem transition_coord (i : Fin 3) :
    transition W j k (overlapCoord W k j i) =
      overlapInverse W j k * overlapCoord W j k i := by
  change IsLocalization.Away.lift (coord W k j) (transitionBase_isUnit W j k)
    (algebraMap _ _ (coord W k i)) = _
  rw [IsLocalization.Away.lift_eq]
  exact transitionBase_coord W j k i

/-- The reverse normalizing inverse maps back to the original coordinate. -/
@[simp] theorem transition_inverse :
    transition W j k (overlapInverse W k j) = overlapCoord W j k k := by
  apply (overlapInverse_isUnit W j k).mul_left_inj.mp
  have h := congrArg (transition W j k) (overlapInverse_mul W k j)
  rw [map_mul, map_one, transition_coord, overlapCoord_self, mul_one] at h
  exact h.trans ((overlapInverse_mul W j k).symm.trans (mul_comm _ _))

/-- The two explicit rescalings are inverse on the whole overlap algebra. -/
theorem transition_comp :
    (transition W j k).comp (transition W k j) = AlgHom.id R (Overlap W j k) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coord W j k))
  apply hom_ext
  intro i
  change transition W j k (transition W k j (overlapCoord W j k i)) =
    overlapCoord W j k i
  rw [transition_coord, map_mul, transition_inverse, transition_coord]
  calc
    overlapCoord W j k k * (overlapInverse W j k * overlapCoord W j k i) =
        (overlapInverse W j k * overlapCoord W j k k) * overlapCoord W j k i := by ring
    _ = overlapCoord W j k i := by rw [overlapInverse_mul, one_mul]

/-- The two localized chart presentations describe the same integral overlap. -/
def overlapEquiv : Overlap W k j ≃ₐ[R] Overlap W j k :=
  AlgEquiv.ofAlgHom (transition W j k) (transition W k j)
    (transition_comp W j k) (transition_comp W k j)

end FLT.Mazur.WeierstrassIntegralChart
