/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalInverse

/-!
# The projective tangent formula for formal doubling

Over the universal characteristic-zero domain, cancellation against the inverse
reduces doubling to a nondegenerate secant. The normalized middle coordinate then
extracts a polynomial identity, which specializes to every coefficient ring.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The generic double differs from the inverse in characteristic zero. -/
theorem add_X_X_ne_negate_X [CharZero R] :
    add W PowerSeries.X PowerSeries.X ≠ negate W (PowerSeries.X : PowerSeries R) := by
  have hx : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by
    simp [PowerSeries.X]
  intro h
  have he := congrArg (PowerSeries.coeff 1) h
  rw [coeff_one_add W hx hx, coeff_one_negate W hx] at he
  norm_num at he

/-- Cancellation in the field group proves the generic tangent comparison. -/
theorem fieldPoint_double_X [IsDomain R] [CharZero R] {K : Type*} [Field K]
    (f : PowerSeries R →+* K) (hf : Function.Injective f) :
    fieldPoint W f hf (add W PowerSeries.X PowerSeries.X)
      (constantCoeff_add W (by simp [PowerSeries.X]) (by simp [PowerSeries.X])) =
      fieldPoint W f hf PowerSeries.X (by simp [PowerSeries.X]) +
        fieldPoint W f hf PowerSeries.X (by simp [PowerSeries.X]) := by
  have hx : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by
    simp [PowerSeries.X]
  have hn := constantCoeff_negate W hx
  have hd := constantCoeff_add W hx hx
  have h := fieldPoint_add_of_ne W f hf hd hn (add_X_X_ne_negate_X W)
  have he : add W (add W PowerSeries.X PowerSeries.X) (negate W PowerSeries.X) =
      (PowerSeries.X : PowerSeries R) := by
    rw [add_assoc W hx hx hn, add_negate W hx, add_zero W hx]
  have hp : fieldPoint W f hf (add W (add W PowerSeries.X PowerSeries.X)
      (negate W PowerSeries.X)) (constantCoeff_add W hd hn) =
      fieldPoint W f hf PowerSeries.X hx := by congr 1
  rw [hp, fieldPoint_negate W f hf hx] at h
  have hc := congrArg (fun Q => Q + fieldPoint W f hf PowerSeries.X hx) h
  simpa only [_root_.add_assoc, neg_add_cancel, _root_.add_zero] using hc.symm

/-- The normalized projective tangent identity over a characteristic-zero domain. -/
theorem dblXYZ_X_of_domain [IsDomain R] [CharZero R] :
    (curve W).toProjective.dblXYZ (representative W (PowerSeries.X : PowerSeries R)) =
      -(curve W).toProjective.dblY (representative W PowerSeries.X) •
        representative W (add W PowerSeries.X PowerSeries.X) := by
  let A := PowerSeries R
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  have hf : Function.Injective f := IsFractionRing.injective A K
  have h := congrArg Point.point (fieldPoint_double_X W f hf)
  change (⟦f ∘ representative W (add W PowerSeries.X PowerSeries.X)⟧ : PointClass K) =
    ((curve W).map f).toProjective.addMap ⟦f ∘ representative W PowerSeries.X⟧
      ⟦f ∘ representative W PowerSeries.X⟧ at h
  rw [addMap_eq, WeierstrassCurve.Projective.add_self, map_dblXYZ] at h
  obtain ⟨u, hu⟩ := Quotient.exact h.symm
  have hy := congrFun hu 1
  change (u : K) * f (-1) =
    f ((curve W).toProjective.dblY (representative W PowerSeries.X)) at hy
  have hy' : -(u : K) = f ((curve W).toProjective.dblY
      (representative W PowerSeries.X)) := by
    simpa only [map_neg, map_one, mul_neg_one] using hy
  have hs : (u : K) = -f ((curve W).toProjective.dblY (representative W PowerSeries.X)) :=
    neg_eq_iff_eq_neg.mp hy'
  funext i
  apply hf
  have hi := congrFun hu i
  simpa only [Function.comp_apply, Units.smul_def, Pi.smul_apply, smul_eq_mul,
    map_mul, map_neg, hs] using hi.symm

end FLT.Mazur.FormalInfinity
