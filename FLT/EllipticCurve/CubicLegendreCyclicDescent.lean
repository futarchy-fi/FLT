/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicCoefficientAction
public import FLT.EllipticCurve.CubicLegendreSwapCover
public import FLT.EllipticCurve.CubicLegendreReciprocalCover
/-! # Descent of the integral Legendre cyclic maps

The coefficient-action comparison and scalar sign independence prove the
actual invariance required for quadratic descent. The resulting maps preserve
the original coefficient base and recover the coordinate transports on the
root covers. This constructs both universal Legendre cyclic maps on the
original base, without retaining a choice of square root.

Inverse and cocycle identities for these descended maps are not proved here. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [IsDomain R] [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
section CoordinateDescent
variable (d : Rˣ) [Fact (IsUnit (2 : R))]
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]
variable (V : WeierstrassCurve R) [V.IsElliptic]

omit [IsNoetherianRing R] [IsDomain R] [Fact (IsUnit (2 : R))]
    [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)] in
/-- The quadratic coefficient involution changes the root sign in the coordinate change. -/
theorem quadraticRootSignChange_map (r : R) :
    (signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r)).map
      (quadraticEtaleNeg d).toRingHom =
        signCoordinateChange (-(quadraticEtaleUnit d)) (algebraMap R (QuadraticEtaleRing d) r) := by
  ext <;> simp [signCoordinateChange, VariableChange.map, quadraticEtaleNeg_unit]

attribute [local irreducible] variableChangeCongrOverIso

omit [Fact (IsUnit (2 : R))] in
/-- Root-sign independence proves invariance under the actual cyclic covering involution. -/
theorem quadraticCoordinateMap_invariant (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d))) :
    quadraticCyclicSign d V p ≫
      ((groupCyclicParameterIso p (variableChangeCongrOverIso
        (W.map (algebraMap R (QuadraticEtaleRing d))) (V.map (algebraMap R (QuadraticEtaleRing d)))
        (signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r))
        h)).hom.left ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p) =
      (groupCyclicParameterIso p (variableChangeCongrOverIso
        (W.map (algebraMap R (QuadraticEtaleRing d))) (V.map (algebraMap R (QuadraticEtaleRing d)))
        (signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r))
        h)).hom.left ≫ coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p := by
  let C := signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r)
  have hm := quadraticRootSignChange_map d r
  have hneg : signCoordinateChange (-(quadraticEtaleUnit d))
      (algebraMap R (QuadraticEtaleRing d) r) • W.map (algebraMap R (QuadraticEtaleRing d)) =
        V.map (algebraMap R (QuadraticEtaleRing d)) := by
    rw [← hm]
    exact coefficientEnd_variableChange_equation W (QuadraticEtaleRing d)
      (quadraticEtaleNeg d) V C h
  have h₁ : (W.map (algebraMap R (QuadraticEtaleRing d))).a₁ = 0 := by
    change algebraMap R (QuadraticEtaleRing d) W.a₁ = 0
    rw [ha₁, map_zero]
  have h₃ : (W.map (algebraMap R (QuadraticEtaleRing d))).a₃ = 0 := by
    change algebraMap R (QuadraticEtaleRing d) W.a₃ = 0
    rw [ha₃, map_zero]
  have hsign := groupCyclicParameterIso_neg p
    (variableChangeCongrOverIso _ _ C h)
    (variableChangeCongrOverIso _ _
      (signCoordinateChange (-(quadraticEtaleUnit d)) (algebraMap R (QuadraticEtaleRing d) r)) hneg)
    (signCoordinateChange_over _ _ h₁ h₃ _ _ h hneg)
  have hc : groupCyclicParameterIso p (variableChangeCongrOverIso _ _
      (C.map (quadraticEtaleNeg d).toRingHom)
      (coefficientEnd_variableChange_equation W (QuadraticEtaleRing d)
        (quadraticEtaleNeg d) V C h)) =
        groupCyclicParameterIso p (variableChangeCongrOverIso _ _ C h) := by
    simpa only [C, quadraticRootSignChange_map] using hsign.symm
  rw [← coefficientCyclicEnd_quadratic, ← Category.assoc,
    coefficientEnd_variableChange_cyclic, hc, Category.assoc, coefficientCyclicEnd_coefficient]

/-- The cyclic coordinate map descended from its quadratic root cover. -/
def quadraticCoordinateDesc (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d))) :
    (scalarQuotientModel V p).left ⟶ (scalarQuotientModel W p).left :=
  quadraticCyclicDesc d V p
    ((groupCyclicParameterIso p (variableChangeCongrOverIso
      (W.map (algebraMap R (QuadraticEtaleRing d))) (V.map (algebraMap R (QuadraticEtaleRing d)))
      (signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d)
        r)) h)).hom.left ≫
        coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p)
    (quadraticCoordinateMap_invariant W p d V ha₁ ha₃ r h)

/-- The descended map recovers the actual coordinate transport over the root cover. -/
@[reassoc (attr := simp)]
theorem quadraticCoordinateDesc_fac (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d))) :
    coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p ≫
      quadraticCoordinateDesc W p d V ha₁ ha₃ r h =
        (groupCyclicParameterIso p (variableChangeCongrOverIso
          (W.map (algebraMap R (QuadraticEtaleRing d))) (V.map (algebraMap R
            (QuadraticEtaleRing d)))
          (signCoordinateChange (quadraticEtaleUnit d)
            (algebraMap R (QuadraticEtaleRing d) r)) h)).hom.left ≫
              coefficientScalarQuotientMorphism W (QuadraticEtaleRing d) p :=
  quadraticCyclicDesc_fac d V p _ _


/-- The descended cyclic coordinate map preserves the coefficient base. -/
theorem quadraticCoordinateDesc_toBase (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d))) :
    quadraticCoordinateDesc W p d V ha₁ ha₃ r h ≫ (scalarQuotientModel W p).hom =
      (scalarQuotientModel V p).hom := by
  apply (cancel_epi (coefficientScalarQuotientMorphism V (QuadraticEtaleRing d) p)).mp
  have he := (groupCyclicParameterIso p (variableChangeCongrOverIso
    (W.map (algebraMap R (QuadraticEtaleRing d))) (V.map (algebraMap R (QuadraticEtaleRing d)))
    (signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r)) h)).hom.w
  rw [← Category.assoc, quadraticCoordinateDesc_fac, Category.assoc,
    coefficientScalarQuotientMorphism_toBase, ← Category.assoc, he,
    coefficientScalarQuotientMorphism_toBase]

/-- The descended map as a morphism over the original coefficient base. -/
def quadraticCoordinateDescOver (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : R)
    (h : signCoordinateChange (quadraticEtaleUnit d) (algebraMap R (QuadraticEtaleRing d) r) •
      W.map (algebraMap R (QuadraticEtaleRing d)) = V.map (algebraMap R (QuadraticEtaleRing d))) :
    scalarQuotientModel V p ⟶ scalarQuotientModel W p :=
  Over.homMk (quadraticCoordinateDesc W p d V ha₁ ha₃ r h)
    (quadraticCoordinateDesc_toBase W p d V ha₁ ha₃ r h)

end CoordinateDescent


section Legendre
/-- The swap coordinate change identifies the two base-extended Legendre equations. -/
theorem legendreSwap_coordinate_equation (p : ℕ) :
    signCoordinateChange (quadraticEtaleUnit (-1 : (LegendreBase p)ˣ))
        (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p) 1) •
      (legendreModel p).map (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) =
        (legendreCurve (1 - legendreParameter p)).map
          (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p)) := by
  simp only [map_one, legendreModel, legendreCurve_map, map_sub]
  exact legendreSwapChange_curve _ _ (legendreSwapRoot_square p)

/-- The reciprocal scaling identifies the two base-extended Legendre equations. -/
theorem legendreReciprocal_coordinate_equation (p : ℕ) :
    signCoordinateChange (quadraticEtaleUnit (legendreParameterUnit p))
        (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p) 0) •
      (legendreModel p).map (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) =
        (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).map
          (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p)) := by
  simp only [map_zero, legendreModel, legendreCurve_map]
  rw [← legendreParameterUnit_val p]
  exact legendreReciprocalChange_curve (legendreReciprocalLiftedParameter p)
    (quadraticEtaleUnit (legendreParameterUnit p)) (legendreReciprocalLiftedRoot_square p)

/-- The integral cyclic swap map over the original universal Legendre base. -/
def legendreSwapDescendedMap (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel (legendreCurve (1 - legendreParameter p)) p).left ⟶
      (scalarQuotientModel (legendreModel p) p).left :=
  quadraticCoordinateDesc (legendreModel p) p (-1 : (LegendreBase p)ˣ)
    (legendreCurve (1 - legendreParameter p)) rfl rfl 1 (legendreSwap_coordinate_equation p)

/-- The integral cyclic reciprocal map over the original universal Legendre base. -/
def legendreReciprocalDescendedMap (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel
      (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p).left ⟶
        (scalarQuotientModel (legendreModel p) p).left :=
  quadraticCoordinateDesc (legendreModel p) p (legendreParameterUnit p)
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    rfl rfl 0 (legendreReciprocal_coordinate_equation p)

/-- The descended cyclic swap as a morphism over the Legendre base. -/
def legendreSwapDescendedOver (p : ℕ) [Fact p.Prime] :
    scalarQuotientModel (legendreCurve (1 - legendreParameter p)) p ⟶
      scalarQuotientModel (legendreModel p) p :=
  quadraticCoordinateDescOver (legendreModel p) p (-1 : (LegendreBase p)ˣ)
    (legendreCurve (1 - legendreParameter p)) rfl rfl 1 (legendreSwap_coordinate_equation p)

/-- The descended cyclic reciprocal map over the Legendre base. -/
def legendreReciprocalDescendedOver (p : ℕ) [Fact p.Prime] :
    scalarQuotientModel
      (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p ⟶
        scalarQuotientModel (legendreModel p) p :=
  quadraticCoordinateDescOver (legendreModel p) p (legendreParameterUnit p)
    (legendreCurve (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    rfl rfl 0 (legendreReciprocal_coordinate_equation p)

/-- The morphism over the base has the specified underlying swap map. -/
theorem legendreSwapDescendedOver_left (p : ℕ) [Fact p.Prime] :
    (legendreSwapDescendedOver p).left = legendreSwapDescendedMap p := rfl

/-- The morphism over the base has the specified underlying reciprocal map. -/
theorem legendreReciprocalDescendedOver_left (p : ℕ) [Fact p.Prime] :
    (legendreReciprocalDescendedOver p).left = legendreReciprocalDescendedMap p := rfl

end Legendre

end WeierstrassCurve.CubicCharts
