/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingMonomialBasis

/-!
# The original relative cubic relation

Expanding the actual square of the order-three lift in the monomial basis
constructs five coefficients in the actual base ring. The cube coefficient
is one, and the lower terms enter through the original order-five inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionPoleMultiplicativeCoordinates Scheme.Modules.pullback
  smoothMarkingMonomialSixBasis smoothMarkingMonomialFiveBasis
  smoothMarkingFramedYSquare smoothMarkingFramedCube

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The structure morphism is proper for the original family. -/
local instance generalizedCurveMarkingCubicRelationProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The five lower cubic coefficients, in order 1, x, y, x², xy. -/
def smoothMarkingCubicCoefficients : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → Γ(S, ⊤) :=
  fun i ↦ (smoothMarkingMonomialSixBasis E s e).repr
    (smoothMarkingFramedYSquare E s e) (Sum.inl i)

/-- The actual square has a unique expansion with unit cube coefficient. -/
theorem smoothMarkingCubicRelation :
    smoothMarkingFramedYSquare E s e =
      (∑ i, smoothMarkingCubicCoefficients E s e i •
        divisorPowerRingStep E.curve.hom.appTop.hom (hI) 5
          (smoothMarkingMonomialFiveBasis E s e i)) +
        smoothMarkingFramedCube E s e := by
  have h := (smoothMarkingMonomialSixBasis E s e).sum_repr
    (smoothMarkingFramedYSquare E s e)
  rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)] at h
  refine h.symm.trans ?_
  rw [smoothMarkingMonomialSixBasis_YSquare_last, one_smul,
    smoothMarkingMonomialSixBasis_new]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smoothMarkingMonomialSixBasis_old]
  rfl

/-- The cubic defect is an actual order-five pole section included by the original map. -/
theorem smoothMarkingCubicDefect :
    smoothMarkingFramedYSquare E s e - smoothMarkingFramedCube E s e =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 5
        (∑ i, smoothMarkingCubicCoefficients E s e i •
          smoothMarkingMonomialFiveBasis E s e i) := by
  rw [smoothMarkingCubicRelation, add_sub_cancel_right, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_smul (divisorPowerRingStep E.curve.hom.appTop.hom (hI) 5) _ _).symm

/-- The constructed five coefficients are uniquely determined by the actual cubic defect. -/
theorem smoothMarkingCubicCoefficients_unique
    (c : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → Γ(S, ⊤))
    (hc : smoothMarkingFramedYSquare E s e - smoothMarkingFramedCube E s e =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 5
        (∑ i, c i • smoothMarkingMonomialFiveBasis E s e i)) :
    c = smoothMarkingCubicCoefficients E s e := by
  have h := divisorPowerRingStep_injective E.curve.hom.appTop.hom (hI) 5
    (hc.symm.trans (smoothMarkingCubicDefect E s e))
  apply (smoothMarkingMonomialFiveBasis E s e).equivFun.symm.injective
  simpa only [Module.Basis.equivFun_symm_apply] using h

end FLT.Mazur.GeneralizedEllipticCurve
