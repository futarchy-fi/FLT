/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioEquiv

/-!
# The corrected full arithmetic node as an open polygon chart

Finite correction supplies a scheme isomorphism on the entire original node.
Its composition with the actual normalized tangent inclusion is an open immersion.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "M" => NodalFiber.TangentOpen τ (-1 : R)
local notation "N" => NodalFiber.Coordinate τ
local notation "F" => polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "E" => polynomialFactorRatioEquiv W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The full corrected arithmetic node is isomorphic to the normalized tangent neighborhood. -/
def polynomialFactorRatioIso : Spec (.of L) ≅ Spec (.of M) :=
  Scheme.Spec.mapIso (E).toRingEquiv.toCommRingCatIso.op

/-- The isomorphism retains exactly the original corrected ring map. -/
theorem polynomialFactorRatioIso_hom :
    (polynomialFactorRatioIso W ha s τ hτ b3 b4 b6 r hr I hI hrI h3).hom =
      Spec.map (CommRingCat.ofHom (F).toRingHom) := rfl

/-- The original whole node embeds in the polygon with the corrected factor-ratio coordinates. -/
def polynomialFactorRatioChart : Spec (.of L) ⟶ PolygonSmoothing.chart R τ :=
  (polynomialFactorRatioIso W ha s τ hτ b3 b4 b6 r hr I hI hrI h3).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap N M)) ≫
      (NodalFiber.unitSmoothingIso τ τ 1 (by simp)).hom

instance polynomialFactorRatioChart_isOpenImmersion :
    IsOpenImmersion (polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N M))) :=
    IsOpenImmersion.of_isLocalization (NodalFiber.q τ + algebraMap R N (-1 : R))
  unfold polynomialFactorRatioChart
  infer_instance

/-- All original coefficient functions are retained by the corrected arithmetic chart. -/
@[reassoc] theorem polynomialFactorRatioChart_structure :
    polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing τ))) =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  simp only [polynomialFactorRatioChart, Category.assoc, NodalFiber.unitSmoothingIso_structure]
  rw [← Spec.map_comp, polynomialFactorRatioIso_hom, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change F (algebraMap N M (algebraMap R N x)) = _
  rw [← IsScalarTower.algebraMap_apply R N M, AlgHom.commutes]
  rfl

end FLT.Mazur.WeierstrassModificationX
