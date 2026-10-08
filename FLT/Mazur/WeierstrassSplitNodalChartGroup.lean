/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalUnitPoints
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The multiplicative group on the original nodal infinity chart

Transport the Laurent group along the explicit isomorphism over the base.
All group laws are proved by transport. The carrier remains the original
normalized cubic chart, whose inclusion in the relative smooth locus has
already been constructed; its identity maps to the original cubic zero.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- The original nodal infinity chart as a scheme over the coefficient spectrum. -/
abbrev splitNodalChartOver : Over (Spec (.of R)) :=
  Over.mk (chartStructure (splitNodalEquation a) 1)

/-- The explicit Laurent comparison transports a group law to the original chart. -/
abbrev splitNodalChartGrpObj : GrpObj (splitNodalChartOver a) :=
  GrpObj.ofIso (splitNodalTorusOverIso a)

/-- The transported group is commutative, by the actual torus commutativity identity. -/
abbrev splitNodalChartCommGrpObj : CommGrpObj (splitNodalChartOver a) where
  __ := splitNodalChartGrpObj a
  mul_comm := by
    change (β_ _ _).hom ≫
      ((splitNodalTorusOverIso a).inv ⊗ₘ (splitNodalTorusOverIso a).inv) ≫
        MonObj.mul ≫ (splitNodalTorusOverIso a).hom = _
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
    rfl

/-- The original cubic chart, with its constructed commutative group structure. -/
def splitNodalChartGroup : CommGrp (Over (Spec (.of R))) := by
  letI := splitNodalChartCommGrpObj a
  exact ⟨splitNodalChartOver a⟩

/-- The group carrier is the original normalized cubic chart. -/
theorem splitNodalChartGroup_carrier : (splitNodalChartGroup a).X = splitNodalChartOver a := rfl

/-- Its multiplication is the explicitly transported Laurent multiplication. -/
theorem splitNodalChartGroup_multiplication :
    let _ := splitNodalChartCommGrpObj a
    μ[splitNodalChartOver a] =
      ((splitNodalTorusOverIso a).inv ⊗ₘ (splitNodalTorusOverIso a).inv) ≫
        μ[MultiplicativeGroupScheme.gm R] ≫ (splitNodalTorusOverIso a).hom := rfl

/-- Its identity is the transported torus identity. -/
theorem splitNodalChartGroup_identity :
    let _ := splitNodalChartCommGrpObj a
    η[splitNodalChartOver a] =
      η[MultiplicativeGroupScheme.gm R] ≫ (splitNodalTorusOverIso a).hom := rfl

/-- Unit one on the torus lands at the original scheme-valued cubic zero section. -/
theorem splitNodalTorus_identity_zero :
    Spec.map (CommRingCat.ofHom
      (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom) ≫ splitNodalTorusToCurve a =
        integralCurveZero (splitNodalEquation a) := by
  change Spec.map _ ≫ Spec.map _ ≫ integralCurveChart (splitNodalEquation a) 1 = _
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (splitNodalUnitChart a (1 : Rˣ)).toRingHom) ≫ _ = _
  rw [splitNodalUnitChart_one]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
