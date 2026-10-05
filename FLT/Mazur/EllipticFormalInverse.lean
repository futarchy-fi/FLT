/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalFirstOrder
public import FLT.Mazur.EllipticFormalGroupLaw

/-!
# The inverse of integral elliptic formal addition

Normalized Weierstrass negation is the inverse for the constructed formal group.
The proof first compares negation in a fraction field, then specializes the
universal coefficient ring and substitutes any zero-constant parameter.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {σ : Type*} (W : WeierstrassCurve R)

/-- The zero parameter maps to the identity of the projective group. -/
theorem fieldPoint_zero [IsDomain R] {K : Type*} [Field K]
    (f : MvPowerSeries σ R →+* K) (hf : Function.Injective f) :
    fieldPoint W f hf 0 (by simp) = 0 := by
  have he : f ∘ representative W 0 = (-1 : K) • ![0, 1, 0] := by
    simp [representative, coordinate_zero, comp_fin3]
  apply Point.ext
  change (⟦f ∘ representative W 0⟧ : PointClass K) = ⟦![0, 1, 0]⟧
  rw [he, smul_eq _ isUnit_one.neg]

/-- Formal negation agrees with negation in the actual projective group. -/
theorem fieldPoint_negate [IsDomain R] {K : Type*} [Field K]
    (f : MvPowerSeries σ R →+* K) (hf : Function.Injective f)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    fieldPoint W f hf (negate W t) (constantCoeff_negate W ht) =
      -fieldPoint W f hf t ht := by
  have hn : (curve W).toProjective.neg (representative W t) =
      ![t, negationDenominator (curve W) t (coordinate W t), coordinate W t] := by
    simp [WeierstrassCurve.Projective.neg, negY, representative, negationDenominator]
  have he := congrArg (fun p : Fin 3 → MvPowerSeries σ R => f ∘ p)
    (hn.trans (negation_representative W ht))
  rw [← WeierstrassCurve.Projective.map_neg, comp_smul] at he
  have hs : IsUnit (f (-negationDenominator (curve W) t (coordinate W t))) :=
    ((MvPowerSeries.isUnit_iff_constantCoeff.mpr
      (constantCoeff_negationDenominator W ht ▸ isUnit_one)).neg).map f
  apply Point.ext
  change (⟦f ∘ representative W (negate W t)⟧ : PointClass K) =
    ((curve W).map f).toProjective.negMap ⟦f ∘ representative W t⟧
  rw [negMap_eq, he, smul_eq _ hs]

/-- In characteristic zero the generic parameter differs from its negative. -/
theorem X_ne_negate_X [CharZero R] : (PowerSeries.X : PowerSeries R) ≠ negate W PowerSeries.X := by
  intro h
  have he := congrArg (PowerSeries.coeff 1) h
  rw [coeff_one_negate W (by simp [PowerSeries.X])] at he
  norm_num at he

/-- The inverse identity over a characteristic-zero domain. -/
theorem add_X_negate_X_of_domain [IsDomain R] [CharZero R] :
    add W PowerSeries.X (negate W PowerSeries.X) = (0 : PowerSeries R) := by
  let A := PowerSeries R
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  have hf : Function.Injective f := IsFractionRing.injective A K
  have ht : MvPowerSeries.constantCoeff (PowerSeries.X : A) = 0 := by simp [PowerSeries.X]
  apply (fieldPoint_eq_iff W f hf (constantCoeff_add W ht (constantCoeff_negate W ht))
    (by simp)).mp
  rw [fieldPoint_add_of_ne W f hf ht (constantCoeff_negate W ht) (X_ne_negate_X W),
    fieldPoint_negate W f hf ht, fieldPoint_zero W f hf, add_neg_cancel]

/-- The inverse identity for the one-variable integral series over any ring. -/
theorem add_X_negate_X :
    add W PowerSeries.X (negate W PowerSeries.X) = (0 : PowerSeries R) := by
  have h := congrArg (MvPowerSeries.map (coefficientSpecialization W))
    (add_X_negate_X_of_domain universalWeierstrass)
  simpa only [map_addition, map_negate, MvPowerSeries.constantCoeff_X, constantCoeff_negate,
    PowerSeries.X, MvPowerSeries.map_X, universalWeierstrass_map, map_zero] using h

/-- Normalized negation is a right inverse for every zero-constant formal parameter. -/
theorem add_negate {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    add W t (negate W t) = 0 := by
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => t) :=
    (PowerSeries.HasSubst.of_constantCoeff_zero ht).const
  have hx : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by
    simp [PowerSeries.X]
  have h := congrArg (MvPowerSeries.substAlgHom ha) (add_X_negate_X W)
  rw [substitution_add W ha (fun _ => ht) hx (constantCoeff_negate W hx),
    substitution_negate W ha (fun _ => ht) hx, map_zero] at h
  simpa [PowerSeries.X, MvPowerSeries.subst_X ha] using h

/-- Normalized negation is also a left inverse. -/
theorem negate_add {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    add W (negate W t) t = 0 := by
  rw [add_comm W (constantCoeff_negate W ht) ht, add_negate W ht]

end FLT.Mazur.FormalInfinity
