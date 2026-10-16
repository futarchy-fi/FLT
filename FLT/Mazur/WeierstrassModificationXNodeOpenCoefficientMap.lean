/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialNodeMaps
public import FLT.Mazur.NodalFiberCoefficientRingMap
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Coefficient change on the full initial node neighborhood

The original coefficient map extends over D(q+a₁), preserving both node
coordinates and the full smoothing. The incidence coordinate is not inverted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s : R)
local notation "U" => W.map f
local notation "N" => NodalFiber.Coordinate s
local notation "N'" => NodalFiber.Coordinate (f s)
local notation "L" => PolynomialNodeOpen W s
local notation "L'" => PolynomialNodeOpen U (f s)
local notation "G" => NodalFiber.coefficientRingMap f s (f s) rfl

/-- The full node coefficient map preserves the actual initial-open denominator. -/
theorem nodeOpenCoefficient_denominator :
    G (NodalFiber.q s + algebraMap R N W.a₁) =
      NodalFiber.q (f s) + algebraMap S N' (U).a₁ := by
  rw [map_add, NodalFiber.coefficientRingMap_q, NodalFiber.coefficientRingMap_algebraMap]
  rfl

/-- The original coefficient map on the whole initial node neighborhood. -/
def nodeOpenCoefficientRingMap : L →+* L' :=
  IsLocalization.Away.lift (NodalFiber.q s + algebraMap R N W.a₁)
    (g := (algebraMap N' L').comp G) (by
      rw [RingHom.comp_apply, nodeOpenCoefficient_denominator]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- Every full node function restricts through the unlocalized coefficient map. -/
theorem nodeOpenCoefficientRingMap_base (z : N) :
    nodeOpenCoefficientRingMap f W s (algebraMap N L z) = algebraMap N' L' (G z) :=
  IsLocalization.Away.lift_eq _ _ _

/-- The full neighborhood map has exactly the original coefficient action. -/
theorem nodeOpenCoefficientRingMap_scalar (a : R) :
    nodeOpenCoefficientRingMap f W s (algebraMap R L a) = algebraMap S L' (f a) := by
  rw [IsScalarTower.algebraMap_apply R N L, nodeOpenCoefficientRingMap_base,
    NodalFiber.coefficientRingMap_algebraMap, ← IsScalarTower.algebraMap_apply S N' L']

/-- The first node function is preserved without inverting the incidence parameter. -/
theorem nodeOpenCoefficientRingMap_p :
    nodeOpenCoefficientRingMap f W s (algebraMap N L (NodalFiber.p s)) =
      algebraMap N' L' (NodalFiber.p (f s)) := by
  rw [nodeOpenCoefficientRingMap_base, NodalFiber.coefficientRingMap_p]

/-- The opposite node function retains every coefficient correction. -/
theorem nodeOpenCoefficientRingMap_q :
    nodeOpenCoefficientRingMap f W s (algebraMap N L (NodalFiber.q s)) =
      algebraMap N' L' (NodalFiber.q (f s)) := by
  rw [nodeOpenCoefficientRingMap_base, NodalFiber.coefficientRingMap_q]

/-- The actual neighborhood inclusion commutes with the full node coefficient map. -/
@[reassoc] theorem nodeOpenCoefficientRingMap_square :
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap N L)) =
        Spec.map (CommRingCat.ofHom (algebraMap N' L')) ≫ Spec.map (CommRingCat.ofHom G) := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h))
    (RingHom.ext (nodeOpenCoefficientRingMap_base f W s))

end FLT.Mazur.WeierstrassModificationX
