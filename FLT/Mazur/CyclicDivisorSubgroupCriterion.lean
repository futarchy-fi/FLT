/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothCyclicDivisorSymmetry

/-!
# The exact subgroup criterion for a cyclic orbit divisor

Multiplication vanishing is necessary and sufficient for the actual cyclic
orbit ideal to be the ideal of a finite subgroup. Unit and inverse closure
are proved from the cyclic marking, rather than imposed as extra hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) [Smooth E.curve.hom]
attribute [local instance] smoothCurveCommGrpObj
variable {n : ℕ} (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- An original subgroup whose actual ideal is the orbit product satisfies multiplication. -/
theorem cyclicDivisorMultiplicationEquation_of_ideal (H : E.FiniteSubgroup n)
    (hI : H.ideal = E.cyclicMarkingIdeal φ) : E.cyclicDivisorMultiplicationEquation φ = 0 := by
  let _ : IsMonHom E.inclusion := smoothCurveInclusion_isMonHom E
  let _ : IsMonHom H.curveMap := inferInstanceAs (IsMonHom (H.inclusion ≫ E.inclusion))
  change ClosedGroupIdeal.multiplicationEquation E.curve (E.cyclicMarkingIdeal φ) = 0
  rw [← hI]
  apply ClosedGroupIdeal.multiplicationEquation_of_group E.curve H.ideal H.curveMap H.idealIso
  apply Over.OverMorphism.ext
  exact H.curveMap.left.toImage_imageι

variable [NeZero n] [SmoothOfRelativeDimension 1 E.curve.hom]

/-- Multiplication alone constructs the finite subgroup on the unchanged orbit divisor. -/
def subgroupOfCyclicMultiplication (h : E.cyclicDivisorMultiplicationEquation φ = 0) :
    E.FiniteSubgroup n := E.cyclicDivisorSubgroup φ (E.cyclicDivisorUnitEquation_zero φ) h
      (E.cyclicDivisorInverseEquation_zero φ)

/-- Construction from multiplication keeps the original ideal, including nilpotents. -/
theorem subgroupOfCyclicMultiplication_ideal
    (h : E.cyclicDivisorMultiplicationEquation φ = 0) :
    (E.subgroupOfCyclicMultiplication φ h).ideal = E.cyclicMarkingIdeal φ :=
  E.cyclicDivisorSubgroup_ideal φ _ _ _

/-- The multiplication equation is equivalent to the actual subgroup condition. -/
theorem cyclicDivisorMultiplicationEquation_iff_subgroup :
    E.cyclicDivisorMultiplicationEquation φ = 0 ↔
      ∃ H : E.FiniteSubgroup n, H.ideal = E.cyclicMarkingIdeal φ := by
  constructor
  · intro h
    exact ⟨E.subgroupOfCyclicMultiplication φ h, E.subgroupOfCyclicMultiplication_ideal φ h⟩
  · rintro ⟨H, hI⟩
    exact E.cyclicDivisorMultiplicationEquation_of_ideal φ H hI

end FLT.Mazur.GeneralizedEllipticCurve
