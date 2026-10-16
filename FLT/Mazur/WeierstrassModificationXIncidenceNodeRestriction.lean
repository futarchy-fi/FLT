/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXIncidenceNodeMap
public import FLT.Mazur.WeierstrassModificationXNodeIncidenceOpen

/-!
# Restricting the exact incidence map to the full initial neighborhood

The original incidence is the first coordinate; the second is the small
factor times the opposite factor. The latter factor is a unit on the whole
neighborhood. These equations alone do not imply an open immersion.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "P" => algebraMap N L (NodalFiber.p s)
local notation "Q" => algebraMap N L (NodalFiber.q s)
local notation "F" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "U" => F (polynomialOppositeFactor W s b3 b4 b6 r)

/-- The exact full node morphism obtained by retaining the original incidence. -/
def incidenceNodeRestriction : N →ₐ[R] L :=
  (F).comp (incidenceNodeMap W s b3 b4 b6)

local notation "H" => incidenceNodeRestriction W s b3 b4 b6 r hr I hI hrI h3

/-- The first restricted coordinate is the full inverse incidence parameter. -/
@[simp] theorem incidenceNodeRestriction_p :
    H (NodalFiber.p s) = polynomialNodeInverseT b3 r I hI hrI h3 W P Q
      (polynomialNodeOpen_unit W s) := by
  simp only [incidenceNodeRestriction, AlgHom.comp_apply, incidenceNodeMap_p]
  exact polynomialNodeEvaluation_t ..

/-- Multiplication by the opposite factor recovers the old first coordinate. -/
theorem incidenceNodeRestriction_p_mul_opposite : H (NodalFiber.p s) * U = P := by
  rw [incidenceNodeRestriction, AlgHom.comp_apply, incidenceNodeMap_p]
  rw [← map_mul]
  exact polynomialNodeEvaluation_first ..

/-- The second restricted coordinate retains the complete opposite factor. -/
@[simp] theorem incidenceNodeRestriction_q : H (NodalFiber.q s) = Q * U := by
  rw [incidenceNodeRestriction, AlgHom.comp_apply, incidenceNodeMap_q]
  rw [polynomialFactors_horizontal W s b3 b4 b6 r hr, map_mul]
  change polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 P Q _ _ _ * U = _
  rw [polynomialNodeEvaluation_small]

/-- The full restricted map preserves the precise original smoothing equation. -/
theorem incidenceNodeRestriction_relation :
    H (NodalFiber.p s) * H (NodalFiber.q s) = algebraMap R L s := by
  rw [← map_mul, NodalFiber.relation, AlgHom.commutes]

/-- Restrict the incidence morphism to the original full initial neighborhood. -/
def incidenceInitialMorphism : Spec (.of L) ⟶ PolygonSmoothing.chart R s :=
  Spec.map (CommRingCat.ofHom ((H).comp (NodalFiber.fromSmoothing s)).toRingHom)

/-- This is the actual restriction of the global original incidence map. -/
@[reassoc] theorem polynomialNodeChart_incidence :
    polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3 ≫
      incidencePolygonMorphism W s b3 b4 b6 =
        incidenceInitialMorphism W s b3 b4 b6 r hr I hI hrI h3 := by
  rw [polynomialNodeChart_eq_spec, incidencePolygonMorphism, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
