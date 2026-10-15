/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNilpotentBranch
public import FLT.Mazur.QuadraticRootBranchChart

/-!
# Any constructed simple slope gives an original polygon node open

This comparison uses the unchanged monic presentation of the original
successive equation. It applies to either root, with explicit coordinate
evaluation and the localization inverse supplying the open immersion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (r : SuccessiveIncidence.Coordinate π)
  (hr : r ^ 2 + nodeSlopeLinear W π b3 * r = nodeSlopeConstant W s π b4 b6)
  (hu : IsUnit (r + r + nodeSlopeLinear W π b3))
local notation "a" => nodeSlopeLinear W π b3
local notation "b" => nodeSlopeConstant W s π b4 b6

/-- Evaluation at any actual root of the original slope equation. -/
def simpleSlopeRetraction : Coordinate W s π b3 b4 b6 →ₐ[R]
    SuccessiveIncidence.Coordinate π :=
  ((QuadraticRootBranchLocalization.evaluation a b r hr).restrictScalars R).comp
    (toMonic W s π b3 b4 b6)

/-- Simple-root evaluation preserves both original incidence coordinates and the slope. -/
@[simp] theorem simpleSlopeRetraction_coord (i : Fin 3) :
    simpleSlopeRetraction W s π b3 b4 b6 r hr (coord W s π b3 b4 b6 i) =
      ![SuccessiveIncidence.t π, r, SuccessiveIncidence.u π] i := by
  change QuadraticRootBranchLocalization.evaluation a b r hr
    (toMonic W s π b3 b4 b6 (coord W s π b3 b4 b6 i)) = _
  rw [toMonic_coord]
  fin_cases i
  · exact (QuadraticRootBranchLocalization.evaluation a b r hr).commutes _
  · exact QuadraticRootBranchLocalization.evaluation_root a b r hr
  · exact (QuadraticRootBranchLocalization.evaluation a b r hr).commutes _

/-- The original incidence projection has the constructed root section as right inverse. -/
theorem simpleSlopeRetraction_incidence :
    (simpleSlopeRetraction W s π b3 b4 b6 r hr).comp
      (incidenceToCoordinate W s π b3 b4 b6) = AlgHom.id R _ := by
  apply SuccessiveIncidence.hom_ext <;>
    simp only [AlgHom.comp_apply, incidenceToCoordinate, SuccessiveIncidence.evaluation_t,
      SuccessiveIncidence.evaluation_u, simpleSlopeRetraction_coord,
      Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      AlgHom.id_apply]

/-- The actual polygon node embeds through the specified original simple slope. -/
def simpleSlopePolygonChart : Spec (.of (PolygonSmoothing.ChartRing π)) ⟶
    Spec (.of (Coordinate W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (SuccessiveIncidence.toPolygon π).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (simpleSlopeRetraction W s π b3 b4 b6 r hr).toRingHom)

include hu in
/-- The entire simple branch is open, using the proved quadratic localization inverse. -/
theorem simpleSlopePolygonChart_isOpenImmersion :
    IsOpenImmersion (simpleSlopePolygonChart W s π b3 b4 b6 r hr) := by
  have hp : IsIso (CommRingCat.ofHom (SuccessiveIncidence.toPolygon π).toRingHom) :=
    (SuccessiveIncidence.polygonEquiv π).toRingEquiv.toCommRingCatIso.isIso_hom
  have hm : IsIso (CommRingCat.ofHom (toMonic W s π b3 b4 b6).toRingHom) :=
    (monicEquiv W s π b3 b4 b6).toRingEquiv.toCommRingCatIso.isIso_hom
  have hb := QuadraticRootBranchLocalization.branchChart_isOpenImmersion a b r hr hu
  simp only [simpleSlopePolygonChart, simpleSlopeRetraction, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp]
  change IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (SuccessiveIncidence.toPolygon π).toRingHom) ≫
      QuadraticRootBranchLocalization.branchChart a b r hr ≫
        Spec.map (CommRingCat.ofHom (toMonic W s π b3 b4 b6).toRingHom))
  exact IsOpenImmersion.comp _ _

/-- The new polygon chart retains the original coefficient structure. -/
@[reassoc] theorem simpleSlopePolygonChart_structure :
    simpleSlopePolygonChart W s π b3 b4 b6 r hr ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s π b3 b4 b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing π))) := by
  simp only [simpleSlopePolygonChart, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact ((SuccessiveIncidence.toPolygon π).comp
    (simpleSlopeRetraction W s π b3 b4 b6 r hr)).commutes x

end FLT.Mazur.WeierstrassSuccessiveX
