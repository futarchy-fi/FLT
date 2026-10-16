/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentMobiusEquiv
public import FLT.Mazur.NodalFiberUnitScalingGeometry

/-!
# A full smoothing-node chart with fractional branch coordinates

The algebraic inverse gives an actual isomorphism of the full tangent opens.
Composing with the target open inclusion gives a genuine polygon chart, with
the original coefficient ring unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (s t : R) (a : Rˣ) (hs : s = (a : R) ^ 2 * t)
local notation "N" => Coordinate t
local notation "L" => TangentOpen s (a : R)
local notation "M" => TangentOpen t (-1 : R)

/-- The full original tangent neighborhood is isomorphic to the fractional-coordinate open. -/
def tangentMobiusIso : Spec (.of L) ≅ Spec (.of M) :=
  Scheme.Spec.mapIso (tangentMobiusEquiv s t a hs).toRingEquiv.toCommRingCatIso.op

/-- The complete fractional-coordinate neighborhood embeds in the actual normalized polygon node. -/
def tangentMobiusChart : Spec (.of L) ⟶ PolygonSmoothing.chart R t :=
  (tangentMobiusIso s t a hs).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap N M)) ≫
    (unitSmoothingIso t t 1 (by simp)).hom

instance tangentMobiusChart_isOpenImmersion :
    IsOpenImmersion (tangentMobiusChart s t a hs) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N M))) :=
    IsOpenImmersion.of_isLocalization (q t + algebraMap R N (-1 : R))
  unfold tangentMobiusChart
  infer_instance

/-- Fractional coordinates preserve all original coefficient functions on the whole chart. -/
@[reassoc] theorem tangentMobiusChart_structure :
    tangentMobiusChart s t a hs ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing t))) =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  simp only [tangentMobiusChart, Category.assoc, unitSmoothingIso_structure]
  rw [← Spec.map_comp]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change tangentMobiusForward s t a hs (algebraMap N M (algebraMap R N r)) = _
  rw [← IsScalarTower.algebraMap_apply R N M, AlgHom.commutes]
  rfl

end FLT.Mazur.NodalFiber
