/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicRingMaps
public import FLT.EllipticCurve.CubicLegendreReciprocalReturn
/-! # Refining the descended reciprocal return

Quadratic coordinate descent is compatible with refinement to an algebra
containing the required root. Applying this to the reciprocal root comparison
identifies the actual descended return map on the original Legendre root cover.
Its coordinate scaling uses the inverse of the original distinguished root.

CubicLegendreReciprocalInvolution uses this factorization to compare the
local semilinear reciprocal with the global automorphism and prove its square
identity. The mixed relation remains separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsDomain R] [IsNoetherianRing S] [IsDomain S]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
variable [Fact (IsUnit (p : S))] [Fact (IsUnit (2 : R))]
variable (d : Rˣ)
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]
variable (V : WeierstrassCurve R) [V.IsElliptic]

@[reassoc]
theorem quadraticCoordinateDesc_refinement_fac
    (σ : QuadraticEtaleRing d →ₐ[R] S)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d)
      (algebraMap R (QuadraticEtaleRing d) r) •
        W.map (algebraMap R (QuadraticEtaleRing d)) =
          V.map (algebraMap R (QuadraticEtaleRing d))) :
    coefficientScalarQuotientMorphism V S p ≫
      quadraticCoordinateDesc W p d V ha₁ ha₃ r h =
        (groupCyclicParameterIso p (variableChangeCongrOverIso
          (W.map (algebraMap R S)) (V.map (algebraMap R S))
          ((signCoordinateChange (quadraticEtaleUnit d)
            (algebraMap R (QuadraticEtaleRing d) r)).map σ.toRingHom)
          (coefficientCompare_variableChange_equation W σ V _ h))).hom.left ≫
            coefficientScalarQuotientMorphism W S p := by
  rw [← coefficientCyclicMap_coefficient V p σ, Category.assoc, quadraticCoordinateDesc_fac,
    ← Category.assoc, coefficientCompare_variableChange_cyclic, Category.assoc,
    coefficientCyclicMap_coefficient]


omit [IsNoetherianRing R] [IsDomain R]
    [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)] in
theorem quadraticReciprocalInvChange_map :
    (legendreReciprocalChange (quadraticEtaleUnit d⁻¹)).map
      (quadraticReciprocalInvHom d).toRingHom =
        legendreReciprocalChange (quadraticEtaleUnit d)⁻¹ := by
  ext <;> simp only [legendreReciprocalChange, VariableChange.map, map_zero,
    Units.coe_map, MonoidHom.coe_ofClass]
  exact congrArg Units.val (quadraticReciprocalInvHom_unit_map d)


theorem legendreReciprocal_return_on_original_equation (p : ℕ) :
    legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹ •
      (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).map
        (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) =
      (legendreModel p).map
        (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) := by
  have h := coefficientCompare_variableChange_equation
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    (quadraticReciprocalInvHom (legendreParameterUnit p)) (legendreModel p)
    (legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p)⁻¹))
    (legendreReciprocal_return_equation p)
  rw [quadraticReciprocalInvChange_map] at h
  exact h

attribute [local irreducible] variableChangeCongrOverIso groupCyclicParameterIso

theorem legendreReciprocalReturn_original_fac (p : ℕ) [Fact p.Prime] :
    ringHomCyclicMap (legendreModel p) p
        (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) ≫
      legendreReciprocalReturnDescendedMap p =
    (groupCyclicParameterIso p (variableChangeCongrOverIso
      ((legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).map
        (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)))
      ((legendreModel p).map
        (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)))
      (legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹)
      (legendreReciprocal_return_on_original_equation p))).hom.left ≫
        ringHomCyclicMap
          (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p
          (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) := by
  have hf := quadraticCoordinateDesc_refinement_fac
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    p (legendreParameterUnit p)⁻¹ (legendreModel p)
    (quadraticReciprocalInvHom (legendreParameterUnit p)) rfl rfl 0
    (by simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using
      legendreReciprocal_return_equation p)
  have hmap :
      (signCoordinateChange (quadraticEtaleUnit (legendreParameterUnit p)⁻¹)
        (algebraMap (LegendreBase p) (LegendreReciprocalReturnRing p) 0)).map
        (quadraticReciprocalInvHom (legendreParameterUnit p)).toRingHom =
          legendreReciprocalChange (quadraticEtaleUnit (legendreParameterUnit p))⁻¹ := by
    simpa only [map_zero, signCoordinateChange, legendreReciprocalChange] using
      quadraticReciprocalInvChange_map (legendreParameterUnit p)
  simpa only [ringHomCyclicMap_algebraMap, legendreReciprocalReturnDescendedMap,
    quadraticReciprocalDesc, hmap] using hf

end WeierstrassCurve.CubicCharts
