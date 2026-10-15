/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveSimpleSlopeChart
public import FLT.Mazur.WeierstrassSuccessiveXBaseChange

/-!
# The constructed polygon slope on the original tensor algebra

The comparison retains the original two tensor boundary coordinates, the
chosen solution of the original slope equation, and every base coefficient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S π) (algebraMap R S b4) (algebraMap R S b6))

local notation "q" => algebraMap R S

/-- Evaluate the original tensor equation at the specified slope, in polygon coordinates. -/
def tensorSlopePolygonRetraction : ScalarExtension W s π b3 b4 b6 S →ₐ[S]
    PolygonSmoothing.ChartRing (q π) :=
  ((SuccessiveIncidence.toPolygon (q π)).comp
    (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr)).comp
      (baseChangeEquiv W s π b3 b4 b6 S).toAlgHom

/-- The actual terminal tensor boundary coordinate is the original left polygon coordinate. -/
theorem tensorSlopePolygonRetraction_left :
    tensorSlopePolygonRetraction W s π b3 b4 b6 S r hr
      (tensorCoord W s π b3 b4 b6 S 0) = PolygonSmoothing.leftCoordinate (q π) := by
  change SuccessiveIncidence.toPolygon (q π)
    (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr
      (baseChangeForward W s π b3 b4 b6 S (tensorCoord W s π b3 b4 b6 S 0))) = _
  rw [baseChangeForward_coord]
  change SuccessiveIncidence.toPolygon (q π)
    (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr
      (coord (W.map q) (q s) (q π) (q b3) (q b4) (q b6) 0)) = _
  simp only [simpleSlopeRetraction_coord, Matrix.cons_val_zero, SuccessiveIncidence.toPolygon_t]

/-- The preceding tensor boundary coordinate is the original right polygon coordinate. -/
theorem tensorSlopePolygonRetraction_right :
    tensorSlopePolygonRetraction W s π b3 b4 b6 S r hr
      (tensorCoord W s π b3 b4 b6 S 2) = PolygonSmoothing.rightCoordinate (q π) := by
  change SuccessiveIncidence.toPolygon (q π)
    (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr
      (baseChangeForward W s π b3 b4 b6 S (tensorCoord W s π b3 b4 b6 S 2))) = _
  rw [baseChangeForward_coord]
  change SuccessiveIncidence.toPolygon (q π)
    (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr
      (coord (W.map q) (q s) (q π) (q b3) (q b4) (q b6) 2)) = _
  rw [simpleSlopeRetraction_coord]
  exact SuccessiveIncidence.toPolygon_u (q π)

/-- The original tensor slope retains the constructed quadratic root. -/
theorem tensorSlopePolygonRetraction_slope :
    tensorSlopePolygonRetraction W s π b3 b4 b6 S r hr
      (tensorCoord W s π b3 b4 b6 S 1) = SuccessiveIncidence.toPolygon (q π) r := by
  change SuccessiveIncidence.toPolygon (q π)
    (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr
      (baseChangeForward W s π b3 b4 b6 S (tensorCoord W s π b3 b4 b6 S 1))) = _
  rw [baseChangeForward_coord]
  change SuccessiveIncidence.toPolygon (q π)
    (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr
      (coord (W.map q) (q s) (q π) (q b3) (q b4) (q b6) 1)) = _
  simp only [simpleSlopeRetraction_coord, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- The tensor evaluation is exactly the existing simple-slope scheme comparison. -/
theorem tensorSlopePolygonRetraction_spec :
    Spec.map (CommRingCat.ofHom
      (tensorSlopePolygonRetraction W s π b3 b4 b6 S r hr).toRingHom) =
        simpleSlopePolygonChart (W.map q) (q s) (q π) (q b3) (q b4) (q b6) r hr ≫
          Spec.map (CommRingCat.ofHom (baseChangeEquiv W s π b3 b4 b6 S).toRingHom) := by
  simp only [tensorSlopePolygonRetraction, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
    Spec.map_comp, simpleSlopePolygonChart, Category.assoc]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
