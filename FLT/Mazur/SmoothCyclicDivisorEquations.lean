/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedGroupIdealGroup
public import FLT.Mazur.CyclicMarkingOrbitDivisor
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# Subgroup equations for the multiplicity-preserving cyclic divisor

On a smooth generalized elliptic curve the full curve inherits its group law.
The closed-group equations therefore apply directly to the original orbit ideal.
When they vanish, the resulting subgroup has that exact ideal and degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) [Smooth E.curve.hom]

/-- The whole smooth curve has the group law of its specified smooth group. -/
@[instance_reducible] def smoothCurveCommGrpObj : CommGrpObj E.curve where
  __ := GrpObj.ofIso (asIso E.inclusion)
  mul_comm := by
    change (β_ _ _).hom ≫ (inv E.inclusion ⊗ₘ inv E.inclusion) ≫
      μ[E.group] ≫ E.inclusion = _
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
    rfl

attribute [local instance] smoothCurveCommGrpObj

/-- The full-curve group structure preserves the original smooth inclusion. -/
instance smoothCurveInclusion_isMonHom : IsMonHom E.inclusion :=
  isMonHom_ofIso (asIso E.inclusion)

variable {n : ℕ} (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- The orbit-divisor unit equation on the original base. -/
def cyclicDivisorUnitEquation := ClosedGroupIdeal.unitEquation E.curve (E.cyclicMarkingIdeal φ)

/-- The orbit-divisor multiplication equation on the entire divisor product. -/
def cyclicDivisorMultiplicationEquation :=
  ClosedGroupIdeal.multiplicationEquation E.curve (E.cyclicMarkingIdeal φ)

/-- The orbit-divisor inverse equation on the full divisor. -/
def cyclicDivisorInverseEquation :=
  ClosedGroupIdeal.inverseEquation E.curve (E.cyclicMarkingIdeal φ)

variable [SmoothOfRelativeDimension 1 E.curve.hom]
  (hu : E.cyclicDivisorUnitEquation φ = 0)
  (hm : E.cyclicDivisorMultiplicationEquation φ = 0)
  (hi : E.cyclicDivisorInverseEquation φ = 0)

/-- Vanishing equations construct an actual finite subgroup, with no etaleness assumption. -/
def cyclicDivisorSubgroup : E.FiniteSubgroup n := by
  letI := ClosedGroupIdeal.commGrpObj E.curve (E.cyclicMarkingIdeal φ) hu hm hi
  letI : IsMonHom (ClosedGroupIdeal.inclusion E.curve (E.cyclicMarkingIdeal φ)) :=
    ClosedGroupIdeal.inclusion_isMonHom E.curve (E.cyclicMarkingIdeal φ) hu hm hi
  letI : IsMonHom E.inclusion := smoothCurveInclusion_isMonHom E
  letI : IsMonHom (inv E.inclusion) :=
    inferInstanceAs (IsMonHom (asIso E.inclusion).inv)
  refine {
    carrier := ClosedGroupIdeal.carrier E.curve (E.cyclicMarkingIdeal φ)
    inclusion := ClosedGroupIdeal.inclusion E.curve (E.cyclicMarkingIdeal φ) ≫ inv E.inclusion
    closed := ?_
    degree := E.cyclicMarkingIdeal_degree φ }
  have : IsIso (inv E.inclusion).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (inv E.inclusion)))
  change IsClosedImmersion ((ClosedGroupIdeal.inclusion E.curve
    (E.cyclicMarkingIdeal φ)).left ≫ (inv E.inclusion).left)
  infer_instance

/-- The constructed subgroup's full curve map is the original divisor immersion. -/
@[reassoc] theorem cyclicDivisorSubgroup_curveMap :
    (E.cyclicDivisorSubgroup φ hu hm hi).curveMap =
      ClosedGroupIdeal.inclusion E.curve (E.cyclicMarkingIdeal φ) := by
  change (_ ≫ inv E.inclusion) ≫ E.inclusion = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The subgroup has precisely the original orbit ideal, including repeated factors. -/
theorem cyclicDivisorSubgroup_ideal :
    (E.cyclicDivisorSubgroup φ hu hm hi).ideal = E.cyclicMarkingIdeal φ := by
  rw [FiniteSubgroup.ideal, cyclicDivisorSubgroup_curveMap]
  exact Scheme.IdealSheafData.ker_subschemeι _

end FLT.Mazur.GeneralizedEllipticCurve
