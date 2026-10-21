/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSmoothSymmetry
public import FLT.Mazur.CompatibleSubgroupIdealIso

/-!
# Multiplication constructs cyclic orbit subgroups on singular curves

Unit and inverse closure come from the cyclic labels. The remaining actual
multiplication equation constructs a finite locally free subgroup whose ideal
on the entire curve is exactly the orbit product, including its multiplicities.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  [SmoothOfRelativeDimension 1 E.group.hom]
  (hm : ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0)

/-- Multiplication closure constructs a subgroup on the entire non-faithful orbit divisor. -/
def singularCyclicDivisorSubgroup : E.FiniteSubgroup n := by
  letI := ClosedGroupIdeal.commGrpObj E.group (E.cyclicMarkingGroupIdeal φ)
    (E.cyclicMarkingGroupIdeal_unitEquation φ) hm (E.cyclicMarkingGroupIdeal_inverseEquation φ)
  letI := ClosedGroupIdeal.inclusion_isMonHom E.group (E.cyclicMarkingGroupIdeal φ)
    (E.cyclicMarkingGroupIdeal_unitEquation φ) hm (E.cyclicMarkingGroupIdeal_inverseEquation φ)
  exact {
    carrier := ClosedGroupIdeal.carrier E.group (E.cyclicMarkingGroupIdeal φ)
    inclusion := ClosedGroupIdeal.inclusion E.group (E.cyclicMarkingGroupIdeal φ)
    degree := E.cyclicMarkingGroupIdeal_degree φ }

/-- The constructed finite subgroup retains the unchanged full-curve orbit ideal. -/
theorem singularCyclicDivisorSubgroup_ideal :
    (E.singularCyclicDivisorSubgroup φ hm).ideal = E.cyclicMarkingIdeal φ := by
  change ((E.cyclicMarkingGroupIdeal φ).subschemeι ≫ E.inclusion.left).ker = _
  rw [← cyclicMarkingGroupCarrierIso_inv_curve,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- Any original subgroup with this orbit ideal is fully compatibly identified with the result. -/
def singularCyclicDivisorOriginalIso (H : E.FiniteSubgroup n)
    (hH : H.ideal = E.cyclicMarkingIdeal φ) :
    FiniteSubgroup.CompatibleIso (E.singularCyclicDivisorSubgroup φ hm) H :=
  FiniteSubgroup.compatibleIsoOfIdealEq _ _
    ((E.singularCyclicDivisorSubgroup_ideal φ hm).trans hH.symm)

end FLT.Mazur.GeneralizedEllipticCurve
