/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineProduct
public import FLT.Mazur.WeierstrassReciprocalAdditionFormula
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Regular addition into the chart containing infinity

A reciprocal slope satisfying the two polynomial relations gives a morphism
into the Y = 1 chart after inverting its homogeneous y-coordinate. In particular,
the construction is defined at reciprocal slope zero, where it gives infinity.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f : AffineProduct W →ₐ[R] S) (m : S)

/-- Homogeneous coordinates of the reciprocal-slope sum on an affine product algebra. -/
def reciprocalCoordinates : Fin 3 → S :=
  reciprocalXYZ (W.map (algebraMap R S))
    (f (productX₁ W)) (f (productX₂ W)) (f (productY₁ W)) m

/-- The principal open where the reciprocal-slope sum lies in the Y = 1 chart. -/
abbrev ReciprocalTargetOpen := Localization.Away (reciprocalCoordinates W f m 1)

/-- Restriction to the open with invertible output y-coordinate. -/
def reciprocalTargetRestriction : S →ₐ[R] ReciprocalTargetOpen W f m :=
  IsScalarTower.toAlgHom R S (ReciprocalTargetOpen W f m)

/-- Inverse of the output y-coordinate. -/
def reciprocalTargetInverse : ReciprocalTargetOpen W f m :=
  ↑(IsLocalization.Away.algebraMap_isUnit (reciprocalCoordinates W f m 1)
    (S := ReciprocalTargetOpen W f m)).unit⁻¹

/-- The normalizing factor cancels the output y-coordinate. -/
@[simp] theorem reciprocalTargetInverse_mul :
    reciprocalTargetInverse W f m *
      reciprocalTargetRestriction W f m (reciprocalCoordinates W f m 1) = 1 :=
  Units.inv_mul_eq_one.mpr
    (IsLocalization.Away.algebraMap_isUnit (reciprocalCoordinates W f m 1)
      (S := ReciprocalTargetOpen W f m)).unit_spec

variable
  (hl : m * (f (productY₁ W) - f (productY₂ W)) = f (productX₁ W) - f (productX₂ W))
  (hc : m * (f (productX₁ W) ^ 2 + f (productX₁ W) * f (productX₂ W) +
      f (productX₂ W) ^ 2 + algebraMap R S W.a₂ * (f (productX₁ W) + f (productX₂ W)) +
      algebraMap R S W.a₄ - algebraMap R S W.a₁ * f (productY₁ W)) =
    f (productY₁ W) + f (productY₂ W) +
      algebraMap R S W.a₁ * f (productX₂ W) + algebraMap R S W.a₃)

include hl hc in
/-- The restricted homogeneous coordinates satisfy the cubic. -/
theorem reciprocalCoordinates_equation :
    (W.map (algebraMap R (ReciprocalTargetOpen W f m))).toProjective.Equation
      (reciprocalTargetRestriction W f m ∘ reciprocalCoordinates W f m) := by
  have h := equation_reciprocalXYZ (W.map (algebraMap R S))
    (productLeft_equation W f) hl hc
  have hr := h.map (reciprocalTargetRestriction W f m).toRingHom
  change ((W.map (algebraMap R S)).map
    (reciprocalTargetRestriction W f m).toRingHom).toProjective.Equation
    (reciprocalTargetRestriction W f m ∘ reciprocalCoordinates W f m) at hr
  have he : (W.map (algebraMap R S)).map
      (reciprocalTargetRestriction W f m).toRingHom =
      W.map (algebraMap R (ReciprocalTargetOpen W f m)) := by
    ext <;> exact (reciprocalTargetRestriction W f m).commutes _
  rw [he] at hr
  exact hr

/-- A regular addition map into the integral chart containing infinity. -/
def reciprocalAddition : Coordinate W 1 →ₐ[R] ReciprocalTargetOpen W f m :=
  evaluation W 1
    (reciprocalTargetInverse W f m •
      (reciprocalTargetRestriction W f m ∘ reciprocalCoordinates W f m))
    (((W.map (algebraMap R (ReciprocalTargetOpen W f m))).toProjective.equation_smul _
      (Units.isUnit _)).mpr (reciprocalCoordinates_equation W f m hl hc))
    (reciprocalTargetInverse_mul W f m)

/-- The chart map has the normalized reciprocal-slope coordinates. -/
@[simp] theorem reciprocalAddition_coord (i : Fin 3) :
    reciprocalAddition W f m hl hc (coord W 1 i) =
      reciprocalTargetInverse W f m *
        reciprocalTargetRestriction W f m (reciprocalCoordinates W f m i) :=
  evaluation_coord W 1 _ _ _ i

/-- Reciprocal slope zero lies in the domain of the infinity chart. -/
theorem reciprocalCoordinates_zero_isUnit : IsUnit (reciprocalCoordinates W f 0 1) := by
  change IsUnit (reciprocalXYZ _ _ _ _ 0 1)
  rw [reciprocalXYZ_zero]
  exact isUnit_one.neg

end FLT.Mazur.WeierstrassIntegralChart
