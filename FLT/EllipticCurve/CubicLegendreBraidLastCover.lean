/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreBraidComparison

/-! # The last reciprocal cover in the Legendre mixed relation

Transport of coefficients identifies the quadratic cover for 1-lambda
with the cover for 1-lambda⁻¹ as rings. The latter is a noetherian domain
and maps to the common cover by sending its root to u*v/w.
The actual last reciprocal coordinate map descends to an isomorphism of
cyclic parameter schemes, with the endpoint required by the mixed relation.
Equality of the full descended composites remains a separate obligation.
-/

@[expose] public noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Transport a quadratic etale ring along an equivalence of coefficient rings. -/
def quadraticCoefficientEquiv (e : R ≃+* S) (d : Rˣ)
    (h2R : IsUnit (2 : R)) (h2S : IsUnit (2 : S)) :
    QuadraticEtaleRing d ≃+* QuadraticEtaleRing (Units.map e.toMonoidHom d) :=
  (quadraticEtaleRootEquiv d h2R).toRingEquiv.trans
    ((AdjoinRoot.mapRingEquiv e (quadraticRootPolynomial d)
      (quadraticRootPolynomial (Units.map e.toMonoidHom d)) (by
        apply Associated.of_eq
        simp [quadraticRootPolynomial])).trans
      (quadraticEtaleRootEquiv (Units.map e.toMonoidHom d) h2S).toRingEquiv.symm)

/-- The unit 1-lambda⁻¹ used by the final reciprocal step. -/
def legendreBraidLastUnit (p : ℕ) : (LegendreBase p)ˣ :=
  Units.map (legendreReciprocalParameterEquiv p).toMonoidHom (legendreComplementUnit p)

theorem legendreBraidLastUnit_val (p : ℕ) :
    (legendreBraidLastUnit p : LegendreBase p) =
      1 - ((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) := by
  change legendreReciprocalParameterMap p (legendreComplementUnit p : LegendreBase p) = _
  rw [legendreComplementUnit_val, map_sub, map_one, legendreReciprocalParameterMap_parameter]

/-- Coefficient transport identifies the complement and last reciprocal covers. -/
def legendreBraidLastCoverEquiv (p : ℕ) :
    QuadraticEtaleRing (legendreComplementUnit p) ≃+*
      QuadraticEtaleRing (legendreBraidLastUnit p) :=
  quadraticCoefficientEquiv (legendreReciprocalParameterEquiv p)
    (legendreComplementUnit p) (legendreBase_units p).1 (legendreBase_units p).1

instance legendreBraidLastDomain (p : ℕ) [NeZero p] :
    IsDomain (QuadraticEtaleRing (legendreBraidLastUnit p)) :=
  Function.Injective.isDomain (legendreBraidLastCoverEquiv p).symm
    (legendreBraidLastCoverEquiv p).symm.injective

instance legendreBraidLastNoetherian (p : ℕ) :
    IsNoetherianRing (QuadraticEtaleRing (legendreBraidLastUnit p)) :=
  IsNoetherianRing.of_finite (LegendreBase p) _

instance legendreBraidLastLevelUnit (p : ℕ) :
    Fact (IsUnit (p : QuadraticEtaleRing (legendreBraidLastUnit p))) :=
  ⟨by
    simpa only [map_natCast] using
      (legendreBase_units p).2.1.map
        (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p)))⟩

/-- The compatible final reciprocal root u*v/w on the common cover. -/
def legendreBraidLastRoot (p : ℕ) : (LegendreBraidRing p)ˣ :=
  legendreBraidRoot (legendreBraidMinusOneRoot p)
    (legendreBraidComplementRoot p) (legendreBraidParameterRoot p)

theorem legendreBraidLastRoot_square (p : ℕ) :
    (legendreBraidLastRoot p : LegendreBraidRing p) ^ 2 =
      algebraMap (LegendreBase p) (LegendreBraidRing p)
        (legendreBraidLastUnit p : LegendreBase p) := by
  have h := legendreBraidRoot_square
    (Units.map (algebraMap (LegendreBase p) (LegendreBraidRing p)).toMonoidHom
      (legendreParameterUnit p))
    (Units.map (algebraMap (LegendreBase p) (LegendreBraidRing p)).toMonoidHom
      (legendreComplementUnit p))
    (legendreBraidMinusOneRoot p) (legendreBraidComplementRoot p) (legendreBraidParameterRoot p)
    (by change algebraMap _ _ (legendreComplementUnit p : LegendreBase p) =
          1 - algebraMap _ _ (legendreParameterUnit p : LegendreBase p)
        rw [legendreComplementUnit_val, legendreParameterUnit_val, map_sub, map_one])
    (legendreBraidMinusOneRoot_square p)
    (by change _ = algebraMap _ _ (legendreComplementUnit p : LegendreBase p)
        rw [legendreComplementUnit_val, map_sub, map_one]
        exact legendreBraidComplementRoot_square p)
    (by change _ = algebraMap _ _ (legendreParameterUnit p : LegendreBase p)
        rw [legendreParameterUnit_val]
        exact legendreBraidParameterRoot_square p)
  rw [legendreBraidLastUnit_val, map_sub, map_one]
  exact h

/-- The last quadratic cover evaluated at its compatible root on the common cover. -/
def legendreBraidLastMap (p : ℕ) :
    QuadraticEtaleRing (legendreBraidLastUnit p) →ₐ[LegendreBase p] LegendreBraidRing p :=
  quadraticUnitLift (legendreBraidLastUnit p) (legendreBraidLastRoot p)
    (legendreBraidChart_units p).1 (legendreBraidLastRoot_square p)

theorem legendreBraidLastMap_root (p : ℕ) :
    legendreBraidLastMap p
      (quadraticEtaleUnit (legendreBraidLastUnit p) : QuadraticEtaleRing _) =
        (legendreBraidLastRoot p : LegendreBraidRing p) :=
  quadraticUnitLift_unit _ _ _ _


theorem unitInverse_sub_one_isUnit (l : Rˣ) (hl : IsUnit ((l : R) - 1)) :
    IsUnit (((l⁻¹ : Rˣ) : R) - 1) := by
  have he : (((l⁻¹ : Rˣ) : R) - 1) * (l : R) = -((l : R) - 1) := by
    rw [sub_mul, Units.inv_mul, one_mul]
    ring
  exact (IsUnit.mul_iff.mp (he ▸ hl.neg)).1

theorem legendreBraidLastUnit_sub_one (p : ℕ) :
    IsUnit ((legendreBraidLastUnit p : LegendreBase p) - 1) := by
  rw [legendreBraidLastUnit_val]
  have he : (1 - ((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) - 1 =
      -((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) := by ring
  rw [he]
  exact (legendreParameterUnit p)⁻¹.isUnit.neg

instance legendreBraidLastElliptic (p : ℕ) :
    (legendreCurve (legendreBraidLastUnit p : LegendreBase p)).IsElliptic :=
  legendreCurve_elliptic _ (legendreBase_units p).1
    (legendreBraidLastUnit p).isUnit (legendreBraidLastUnit_sub_one p)

instance legendreBraidLastInverseElliptic (p : ℕ) :
    (legendreCurve
      (((legendreBraidLastUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).IsElliptic :=
  legendreCurve_elliptic _ (legendreBase_units p).1
    (legendreBraidLastUnit p)⁻¹.isUnit
    (unitInverse_sub_one_isUnit _ (legendreBraidLastUnit_sub_one p))

theorem legendreBraidLast_equation (p : ℕ) :
    signCoordinateChange (quadraticEtaleUnit (legendreBraidLastUnit p))
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p)) 0) •
        (legendreCurve (legendreBraidLastUnit p : LegendreBase p)).map
          (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p))) =
    (legendreCurve (((legendreBraidLastUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)).map
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p))) := by
  have h := legendreReciprocalChange_curve
    (Units.map (algebraMap (LegendreBase p)
      (QuadraticEtaleRing (legendreBraidLastUnit p))).toMonoidHom (legendreBraidLastUnit p))
    (quadraticEtaleUnit (legendreBraidLastUnit p))
    (quadraticEtaleUnit_square (legendreBraidLastUnit p))
  simpa [signCoordinateChange, legendreReciprocalChange, legendreCurve_map] using h

open AlgebraicGeometry CategoryTheory
/-- The actual last reciprocal map on cyclic parameter schemes. -/
def legendreBraidLastDescendedMap (p : ℕ) [Fact p.Prime] :
    (scalarQuotientModel
      (legendreCurve (((legendreBraidLastUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p).left ⟶
        (scalarQuotientModel (legendreCurve (legendreBraidLastUnit p : LegendreBase p)) p).left :=
  quadraticCoordinateDesc (legendreCurve (legendreBraidLastUnit p : LegendreBase p))
    p (legendreBraidLastUnit p)
    (legendreCurve (((legendreBraidLastUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    rfl rfl 0 (legendreBraidLast_equation p)


theorem legendreBraidLastUnit_eq (p : ℕ) :
    legendreBraidLastUnit p =
      (-legendreComplementUnit p) * (legendreParameterUnit p)⁻¹ := by
  apply Units.ext
  rw [legendreBraidLastUnit_val, Units.val_mul, Units.val_neg, legendreComplementUnit_val]
  have h : (legendreParameterUnit p : LegendreBase p) *
      (((legendreParameterUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) = 1 := by simp
  rw [legendreParameterUnit_val] at h
  linear_combination -h

theorem legendreBraidLast_endpoint (p : ℕ) :
    (((legendreBraidLastUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) =
      1 - (((legendreComplementUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p) := by
  rw [legendreBraidLastUnit_eq]
  exact (legendreBraidParameter (legendreParameterUnit p) (legendreComplementUnit p)
    (by rw [legendreComplementUnit_val, legendreParameterUnit_val])).symm

theorem legendreBraidLastMap_coordinate (p : ℕ) :
    (signCoordinateChange (quadraticEtaleUnit (legendreBraidLastUnit p))
      (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreBraidLastUnit p)) 0)).map
        (legendreBraidLastMap p).toRingHom =
      legendreReciprocalChange (legendreBraidLastRoot p) := by
  ext <;> simp only [signCoordinateChange, legendreReciprocalChange,
    VariableChange.map, map_zero]
  change legendreBraidLastMap p
    (quadraticEtaleUnit (legendreBraidLastUnit p) : QuadraticEtaleRing _) = _
  exact legendreBraidLastMap_root p

instance legendreBraidLastDescendedMapIsIso (p : ℕ) [Fact p.Prime] :
    IsIso (legendreBraidLastDescendedMap p) :=
  quadraticCoordinateDescIsIso
    (legendreCurve (legendreBraidLastUnit p : LegendreBase p))
    (legendreCurve (((legendreBraidLastUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p))
    p (legendreBraidLastUnit p) rfl rfl 0 (legendreBraidLast_equation p)

theorem legendreBraidLastDescendedMap_toBase (p : ℕ) [Fact p.Prime] :
    legendreBraidLastDescendedMap p ≫
      (scalarQuotientModel (legendreCurve (legendreBraidLastUnit p : LegendreBase p)) p).hom =
    (scalarQuotientModel
      (legendreCurve (((legendreBraidLastUnit p)⁻¹ : (LegendreBase p)ˣ) : LegendreBase p)) p).hom :=
  quadraticCoordinateDesc_toBase _ _ _ _ rfl rfl 0 (legendreBraidLast_equation p)



end WeierstrassCurve.CubicCharts
