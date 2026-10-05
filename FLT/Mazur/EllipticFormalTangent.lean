/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalDoubling

/-!
# Integral tangent comparison in every characteristic

Specialization from the universal curve and formal substitution extend the
generic tangent identity to all coefficient rings and zero-constant parameters.
Its scale is a unit, so it remains valid under noninjective evaluation.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Mapping coefficients commutes with normalized formal representatives. -/
theorem map_representative {S : Type*} [CommRing S] (f : R →+* S) {σ : Type*}
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    MvPowerSeries.map f ∘ representative W t =
      representative (W.map f) (MvPowerSeries.map f t) := by
  simp only [representative, comp_fin3, map_neg, map_one, map_coordinate W f ht]

/-- Formal substitution commutes with normalized representatives. -/
theorem substitution_representative {σ τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    MvPowerSeries.substAlgHom ha ∘ representative W t =
      representative W (MvPowerSeries.substAlgHom ha t) := by
  simp only [representative, comp_fin3, map_neg, map_one, substitution_coordinate W ha ht]

/-- The one-variable tangent identity holds over every coefficient ring. -/
theorem dblXYZ_X :
    (curve W).toProjective.dblXYZ (representative W (PowerSeries.X : PowerSeries R)) =
      -(curve W).toProjective.dblY (representative W PowerSeries.X) •
        representative W (add W PowerSeries.X PowerSeries.X) := by
  let f := MvPowerSeries.map (σ := Unit) (coefficientSpecialization W)
  have hx : MvPowerSeries.constantCoeff
      (PowerSeries.X : PowerSeries (MvPolynomial (Fin 5) ℤ)) = 0 := by simp [PowerSeries.X]
  have hc : (curve universalWeierstrass).toProjective.map f =
      (curve (σ := Unit) W).toProjective := by
    simp only [curve, WeierstrassCurve.map_map]
    change universalWeierstrass.map (f.comp MvPowerSeries.C) = _
    rw [show f.comp MvPowerSeries.C = MvPowerSeries.C.comp (coefficientSpecialization W) by
      apply RingHom.ext; intro a; exact MvPowerSeries.map_C (coefficientSpecialization W) a]
    rw [← WeierstrassCurve.map_map, universalWeierstrass_map]
  have hp : f ∘ representative universalWeierstrass PowerSeries.X =
      representative W PowerSeries.X := by
    rw [map_representative universalWeierstrass _ hx]
    simp only [universalWeierstrass_map, PowerSeries.X, MvPowerSeries.map_X]
  have hp2 : f ∘ representative universalWeierstrass
      (add universalWeierstrass PowerSeries.X PowerSeries.X) =
      representative W (add W PowerSeries.X PowerSeries.X) := by
    rw [map_representative universalWeierstrass _ (constantCoeff_add _ hx hx)]
    rw [map_addition universalWeierstrass _ hx hx, universalWeierstrass_map]
    simp only [PowerSeries.X, MvPowerSeries.map_X]
  have h := congrArg (fun p : Fin 3 → PowerSeries (MvPolynomial (Fin 5) ℤ) => f ∘ p)
    (dblXYZ_X_of_domain universalWeierstrass)
  rw [← map_dblXYZ, comp_smul, map_neg, ← map_dblY, hc, hp, hp2] at h
  exact h

/-- The projective doubling formula represents formal doubling at every parameter. -/
theorem dblXYZ_representative {σ : Type*} {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) :
    (curve W).toProjective.dblXYZ (representative W t) =
      -(curve W).toProjective.dblY (representative W t) • representative W (add W t t) := by
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => t) :=
    (PowerSeries.HasSubst.of_constantCoeff_zero ht).const
  let f := (MvPowerSeries.substAlgHom (R := R) ha).toRingHom
  have hx : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by
    simp [PowerSeries.X]
  have hc : (curve W).toProjective.map f = (curve (σ := σ) W).toProjective := by
    simp only [curve, WeierstrassCurve.map_map]
    congr 1
    apply RingHom.ext
    intro a
    simp only [f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]
  have hp : f ∘ representative W PowerSeries.X = representative W t := by
    change MvPowerSeries.substAlgHom ha ∘ _ = _
    rw [substitution_representative W ha hx]
    simp only [PowerSeries.X, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  have hp2 : f ∘ representative W (add W PowerSeries.X PowerSeries.X) =
      representative W (add W t t) := by
    change MvPowerSeries.substAlgHom ha ∘ _ = _
    rw [substitution_representative W ha (constantCoeff_add W hx hx),
      substitution_add W ha (fun _ => ht) hx hx]
    simp only [PowerSeries.X, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  have h := congrArg (fun p : Fin 3 → PowerSeries R => f ∘ p) (dblXYZ_X W)
  rw [← map_dblXYZ, comp_smul, map_neg, ← map_dblY, hc, hp, hp2] at h
  exact h

/-- The tangent's normalizing scalar is a unit in the formal series ring. -/
theorem isUnit_doublingScale {σ : Type*} {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) : IsUnit (-(curve W).toProjective.dblY (representative W t)) := by
  apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
  have hc : (curve (σ := σ) W).toProjective.map MvPowerSeries.constantCoeff = W.toProjective := by
    simp [curve, WeierstrassCurve.map_map]
  have hp : MvPowerSeries.constantCoeff ∘ representative W t = ![0, -1, 0] := by
    simp [representative, comp_fin3, ht, constantCoeff_coordinate W ht]
  rw [map_neg, ← map_dblY, hc, hp]
  simp [dblY, negY, dblX, negDblY, dblZ]

end FLT.Mazur.FormalInfinity
