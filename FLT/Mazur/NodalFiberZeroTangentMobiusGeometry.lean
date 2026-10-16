/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberZeroTangentMobiusEquiv
public import FLT.Mazur.NodalFiberUnitScalingGeometry

/-!
# A full zero-node chart with fractional branch coordinates

The algebraic inverse gives an actual isomorphism of the full tangent opens.
Composing with the target open inclusion gives a genuine polygon chart, with
the original coefficient ring unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (a : Rˣ)
local notation "N" => Coordinate (0 : R)
local notation "L" => ZeroTangentOpen (a : R)
local notation "M" => ZeroTangentOpen (-1 : R)

/-- The full original tangent neighborhood is isomorphic to the fractional-coordinate open. -/
def zeroTangentMobiusIso : Spec (.of L) ≅ Spec (.of M) :=
  Scheme.Spec.mapIso (zeroTangentMobiusEquiv a).toRingEquiv.toCommRingCatIso.op

/-- The complete fractional-coordinate neighborhood embeds in the actual zero polygon node. -/
def zeroTangentMobiusChart : Spec (.of L) ⟶ PolygonSmoothing.chart R 0 :=
  (zeroTangentMobiusIso a).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap N M)) ≫
    (unitSmoothingIso (0 : R) 0 1 (by simp)).hom

instance zeroTangentMobiusChart_isOpenImmersion :
    IsOpenImmersion (zeroTangentMobiusChart a) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap N M))) :=
    IsOpenImmersion.of_isLocalization (q (0 : R) + algebraMap R N (-1 : R))
  unfold zeroTangentMobiusChart
  infer_instance

/-- Fractional coordinates preserve all original coefficient functions on the whole chart. -/
@[reassoc] theorem zeroTangentMobiusChart_structure :
    zeroTangentMobiusChart a ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing (0 : R)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  simp only [zeroTangentMobiusChart, Category.assoc, unitSmoothingIso_structure]
  rw [← Spec.map_comp]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change zeroTangentMobiusForward a (algebraMap N M (algebraMap R N r)) = _
  rw [← IsScalarTower.algebraMap_apply R N M, AlgHom.commutes]
  rfl

end FLT.Mazur.NodalFiber
