/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberZeroTangentMobiusBoundary
public import FLT.Mazur.WeierstrassModificationXZeroIdealBoundary

/-!
# Fractional coordinates on the actual initial zero-fiber node

The full original node D(q+a₁) embeds in the zero polygon using p/a₁ and
q/(q+a₁). The original Laurent restriction has the exact required boundary.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)

/-- The original tangent unit with value definitionally equal to the curve coefficient. -/
def zeroInitialTangentUnit : Rˣ :=
  ha.unit.copy W.a₁ ha.unit_spec.symm (↑ha.unit⁻¹ : R) rfl

/-- A full fractional chart on the original initial node, including its intersection point. -/
def zeroInitialMobiusChart : Spec (.of (PolynomialNodeOpen W 0)) ⟶
    PolygonSmoothing.chart R 0 :=
  NodalFiber.zeroTangentMobiusChart (zeroInitialTangentUnit W ha)

instance zeroInitialMobiusChart_isOpenImmersion :
    IsOpenImmersion (zeroInitialMobiusChart W ha) :=
  NodalFiber.zeroTangentMobiusChart_isOpenImmersion _

/-- The genuine fractional chart retains the original arithmetic coefficient structure. -/
@[reassoc] theorem zeroInitialMobiusChart_structure :
    zeroInitialMobiusChart W ha ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing (0 : R)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (PolynomialNodeOpen W 0))) :=
  NodalFiber.zeroTangentMobiusChart_structure _

variable (b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I) (hbot : I = ⊥)
local notation "G" => laurentNodeRestriction W 0 b3 b4 b6 I hI ha (I.zero_mem) h2 h3 h4 h6

include hbot in
/-- The fractional chart preserves the original retained boundary without reparametrization. -/
@[reassoc] theorem zeroInitialMobiusChart_boundary :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫ zeroInitialMobiusChart W ha =
      (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.leftBranchOpen R 0 := by
  exact NodalFiber.zeroTangentMobiusChart_boundary (zeroInitialTangentUnit W ha) G
    (laurentNodeRestriction_p_of_bot W 0 b3 b4 b6 I hI ha (I.zero_mem)
      h2 h3 h4 h6 hbot)
    (laurentNodeRestriction_q_of_bot W 0 b3 b4 b6 I hI ha (I.zero_mem)
      h2 h3 h4 h6 hbot)

end FLT.Mazur.WeierstrassModificationX
