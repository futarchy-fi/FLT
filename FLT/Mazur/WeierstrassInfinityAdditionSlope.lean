/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula
public import FLT.Mazur.WeierstrassProjectiveChartProduct
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A regular divided-difference slope near the pair of infinity points

Invert the dz/dx denominator in the actual tensor product of the two Y = 1
charts. The resulting slope satisfies both polynomial relations needed for
the integral addition formula, including on the diagonal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (W : WeierstrassCurve R)

/-- The left input coordinates after an arbitrary specialization of the Y-chart product. -/
def infinityLeft (f : ChartProduct W 1 1 →ₐ[R] S) : Fin 3 → S :=
  f ∘ chartProductLeft W 1 1 ∘ coord W 1

/-- The right input coordinates after specialization of the Y-chart product. -/
def infinityRight (f : ChartProduct W 1 1 →ₐ[R] S) : Fin 3 → S :=
  f ∘ chartProductRight W 1 1 ∘ coord W 1

/-- The left Y coordinate remains one. -/
@[simp] theorem infinityLeft_one (f : ChartProduct W 1 1 →ₐ[R] S) :
    infinityLeft W f 1 = 1 := by simp only [infinityLeft, Function.comp_apply, coord_self,
      map_one]

/-- The right Y coordinate remains one. -/
@[simp] theorem infinityRight_one (f : ChartProduct W 1 1 →ₐ[R] S) :
    infinityRight W f 1 = 1 := by simp only [infinityRight, Function.comp_apply, coord_self,
      map_one]

/-- The left input satisfies the Y-chart cubic. -/
theorem infinityLeft_equation (f : ChartProduct W 1 1 →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation
      ![infinityLeft W f 0, 1, infinityLeft W f 2] := by
  have h := chartProductLeft_equation W 1 1 f
  change (W.map (algebraMap R S)).toProjective.Equation (infinityLeft W f) at h
  have he := Projective.fin3_def (infinityLeft W f)
  rw [infinityLeft_one] at he
  rwa [he]

/-- The right input satisfies the Y-chart cubic. -/
theorem infinityRight_equation (f : ChartProduct W 1 1 →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation
      ![infinityRight W f 0, 1, infinityRight W f 2] := by
  have h := chartProductRight_equation W 1 1 f
  change (W.map (algebraMap R S)).toProjective.Equation (infinityRight W f) at h
  have he := Projective.fin3_def (infinityRight W f)
  rw [infinityRight_one] at he
  rwa [he]

/-- The dz/dx denominator evaluated on the two universal inputs. -/
def infinityDen (f : ChartProduct W 1 1 →ₐ[R] S) : S :=
  infinitySlopeDenominator (W.map (algebraMap R S))
    (infinityRight W f 0) (infinityLeft W f 2) (infinityRight W f 2)

/-- The dz/dx numerator evaluated on the universal inputs. -/
def infinityNum (f : ChartProduct W 1 1 →ₐ[R] S) : S :=
  infinitySlopeNumerator (W.map (algebraMap R S))
    (infinityLeft W f 0) (infinityRight W f 0) (infinityLeft W f 2)

/-- The denominator commutes with every further restriction of the input product. -/
theorem infinityDen_map (f : ChartProduct W 1 1 →ₐ[R] S) (g : S →ₐ[R] T) :
    g (infinityDen W f) = infinityDen W (g.comp f) := by
  simp only [infinityDen, infinitySlopeDenominator, infinityLeft, infinityRight,
    Function.comp_apply, AlgHom.comp_apply, WeierstrassCurve.map,
    map_sub, map_add, map_mul, map_pow, map_one, AlgHom.commutes]

/-- The numerator also commutes with every further restriction. -/
theorem infinityNum_map (f : ChartProduct W 1 1 →ₐ[R] S) (g : S →ₐ[R] T) :
    g (infinityNum W f) = infinityNum W (g.comp f) := by
  simp only [infinityNum, infinitySlopeNumerator, infinityLeft, infinityRight,
    Function.comp_apply, AlgHom.comp_apply, WeierstrassCurve.map,
    map_sub, map_add, map_mul, map_pow, AlgHom.commutes]

/-- The first open neighborhood, obtained by inverting the divided-difference denominator. -/
abbrev InfinitySlopeOpen := Localization.Away (infinityDen W (AlgHom.id R _))

/-- Restriction to the dz/dx domain. -/
def infinitySlopeRestriction : ChartProduct W 1 1 →ₐ[R] InfinitySlopeOpen W :=
  IsScalarTower.toAlgHom R (ChartProduct W 1 1) (InfinitySlopeOpen W)

/-- The chosen denominator is a unit in this neighborhood. -/
theorem infinityDen_isUnit : IsUnit (infinityDen W (infinitySlopeRestriction W)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (infinityDen W (AlgHom.id R _))
    (S := InfinitySlopeOpen W)
  change IsUnit (infinitySlopeRestriction W (infinityDen W (AlgHom.id R _))) at h
  simpa only [infinityDen_map, AlgHom.comp_id] using h

/-- The regular slope, defined without inverting either difference of input coordinates. -/
def infinitySlope : InfinitySlopeOpen W :=
  ↑(infinityDen_isUnit W).unit⁻¹ * infinityNum W (infinitySlopeRestriction W)

/-- The regular slope satisfies its defining divided-difference relation. -/
theorem infinitySlope_mul_den :
    infinitySlope W * infinityDen W (infinitySlopeRestriction W) =
      infinityNum W (infinitySlopeRestriction W) := by
  have hi : (↑(infinityDen_isUnit W).unit⁻¹ : InfinitySlopeOpen W) *
      infinityDen W (infinitySlopeRestriction W) = 1 :=
    Units.inv_mul_eq_one.mpr (infinityDen_isUnit W).unit_spec
  dsimp only [infinitySlope]
  linear_combination infinityNum W (infinitySlopeRestriction W) * hi

/-- The line through the two inputs is also valid on the diagonal of this neighborhood. -/
theorem infinitySlope_mul_difference :
    infinitySlope W * (infinityRight W (infinitySlopeRestriction W) 0 -
      infinityLeft W (infinitySlopeRestriction W) 0) =
      infinityRight W (infinitySlopeRestriction W) 2 -
        infinityLeft W (infinitySlopeRestriction W) 2 :=
  infinity_slope_relation _ (infinityLeft_equation W _) (infinityRight_equation W _)
    (infinityDen_isUnit W) (infinitySlope_mul_den W)

end FLT.Mazur.WeierstrassIntegralChart
