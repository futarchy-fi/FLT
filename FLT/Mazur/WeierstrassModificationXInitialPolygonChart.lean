/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOpenCoefficientMap
public import FLT.Mazur.NodalFiberUnitScalingGeometry

/-!
# The original full initial neighborhood in its thick polygon chart

The comparison retains the original smoothing s and the full open D(q+a₁).
In the arithmetic application s is the image of π^start, not implicitly π.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s

/-- Map the full original initial neighborhood to the polygon with its actual thickness. -/
def initialPolygonChart : Spec (.of L) ⟶ PolygonSmoothing.chart R s :=
  Spec.map (CommRingCat.ofHom (algebraMap N L)) ≫
    (NodalFiber.unitSmoothingIso s s 1 (by simp)).hom

instance initialPolygonChart_isOpenImmersion : IsOpenImmersion (initialPolygonChart W s) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N L))) :=
    IsOpenImmersion.of_isLocalization (NodalFiber.q s + algebraMap R N W.a₁)
  exact IsOpenImmersion.comp _ _

/-- The full initial comparison preserves the original coefficient structure. -/
@[reassoc] theorem initialPolygonChart_structure :
    initialPolygonChart W s ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing s))) =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [initialPolygonChart, Category.assoc, NodalFiber.unitSmoothingIso_structure,
    ← Spec.map_comp]
  rfl

/-- The exact image retains the original deleted tangent divisor. -/
theorem initialPolygonChart_range :
    Set.range (initialPolygonChart W s) =
      (PrimeSpectrum.basicOpen (PolygonSmoothing.rightCoordinate s +
        algebraMap R (PolygonSmoothing.ChartRing s) W.a₁) : Set (PrimeSpectrum _)) := by
  change Set.range ((NodalFiber.unitSmoothingIso s s 1 (by simp)).hom ∘
    PrimeSpectrum.comap (algebraMap N L)) = _
  rw [Set.range_comp, PrimeSpectrum.localization_away_comap_range L
    (NodalFiber.q s + algebraMap R N W.a₁)]
  rw [← Scheme.coe_homeoOfIso, Homeomorph.image_eq_preimage_symm]
  ext x
  change (NodalFiber.unitSmoothingEquiv s s 1 (by simp)
    (NodalFiber.q s + algebraMap R N W.a₁) ∉ x.asIdeal) ↔ _
  rw [map_add, NodalFiber.unitSmoothingEquiv_q, AlgEquiv.commutes]
  rfl

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- The full thick initial comparison follows every original coefficient substitution. -/
@[reassoc] theorem initialPolygonChart_coefficients :
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫
      initialPolygonChart W s =
        initialPolygonChart (W.map f) (f s) ≫
          Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f s (f s) rfl)) := by
  rw [initialPolygonChart, ← Category.assoc, nodeOpenCoefficientRingMap_square,
    Category.assoc]
  rw [NodalFiber.unitSmoothingIso_coefficients s s 1 (by simp) f
    (f s) (f s) 1 (by simp) rfl rfl (by simp)]
  rw [← Category.assoc]
  rfl

end FLT.Mazur.WeierstrassModificationX
