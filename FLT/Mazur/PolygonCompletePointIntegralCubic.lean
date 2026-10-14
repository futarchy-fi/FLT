/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIntegralMonomials

/-!
# The original relative cubic relation

Expanding the actual square of the order-three lift in the monomial basis
constructs five coefficients in the actual base ring. The cube coefficient
is one, and the lower terms enter through the original order-five inclusion.

These coefficients lie in the original complete-base section ring.
No group law or smoothness of the uncontracted polygon is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor completePointSixMonomialBasis
  completePointFiveMonomialBasis completePointPoleYSquare completePointPoleCube

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)

/-- The five lower cubic coefficients, in order 1, x, y, x², xy. -/
def completePointCubicCoefficients :
    ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → Γ(Spec (.of (PowerSeries K)), ⊤) :=
  fun j ↦ (completePointSixMonomialBasis K n h i).repr
    (completePointPoleYSquare K n h i) (Sum.inl j)

/-- The actual square has a unique expansion with unit cube coefficient. -/
theorem completePointCubicRelation :
    completePointPoleYSquare K n h i =
      (show ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
          (tensorPower (completePointLine K n h i) 6) 0 from
        ∑ j, completePointCubicCoefficients K n h i j •
          divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
            (completeBaseMarking_relativeCartier K n h i).1 5
            (completePointFiveMonomialBasis K n h i j)) +
        completePointPoleCube K n h i := by
  have heq := (completePointSixMonomialBasis K n h i).sum_repr
    (completePointPoleYSquare K n h i)
  rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)] at heq
  refine heq.symm.trans ?_
  rw [completePointSixMonomialBasis_YSquare_last, one_smul,
    completePointSixMonomialBasis_new]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [completePointSixMonomialBasis_old]
  rfl

/-- The cubic defect is an actual order-five pole section included by the original map. -/
theorem completePointCubicDefect :
    completePointPoleYSquare K n h i - completePointPoleCube K n h i =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 5
        (∑ j, completePointCubicCoefficients K n h i j •
          completePointFiveMonomialBasis K n h i j) := by
  rw [completePointCubicRelation, add_sub_cancel_right, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (map_smul (divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 5) _ _).symm

/-- The constructed five coefficients are uniquely determined by the actual cubic defect. -/
theorem completePointCubicCoefficients_unique
    (c : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → Γ(Spec (.of (PowerSeries K)), ⊤))
    (hc : completePointPoleYSquare K n h i - completePointPoleCube K n h i =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 5
        (∑ j, c j • completePointFiveMonomialBasis K n h i j)) :
    c = completePointCubicCoefficients K n h i := by
  have heq := divisorPowerRingStep_injective (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 5
    (hc.symm.trans (completePointCubicDefect K n h i))
  apply (completePointFiveMonomialBasis K n h i).equivFun.symm.injective
  simpa only [Module.Basis.equivFun_symm_apply] using heq

end FLT.Mazur.PolygonInfinitesimalStages
