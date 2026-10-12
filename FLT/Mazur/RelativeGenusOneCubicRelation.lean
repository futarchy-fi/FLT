/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneMonomialBasis

/-!
# The original relative cubic relation

Expanding the actual square of the order-three lift in the monomial basis
constructs five coefficients in the actual base ring. The cube coefficient
is one, and the lower terms enter through the original order-five inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePointMonomialSixBasis relativePointMonomialFiveBasis
  relativePointFramedYSquare relativePointFramedCube

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

/-- The five lower cubic coefficients, in order 1, x, y, x², xy. -/
def relativePointCubicCoefficients : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → Γ(S, ⊤) :=
  fun i ↦ (relativePointMonomialSixBasis G hg s hI e).repr
    (relativePointFramedYSquare G hg s hI e) (Sum.inl i)

/-- The actual square has a unique expansion with unit cube coefficient. -/
theorem relativePointCubicRelation :
    relativePointFramedYSquare G hg s hI e =
      (∑ i, relativePointCubicCoefficients G hg s hI e i •
        divisorPowerRingStep G.hom.appTop.hom hI 5
          (relativePointMonomialFiveBasis G hg s hI e i)) +
        relativePointFramedCube G hg s hI e := by
  have h := (relativePointMonomialSixBasis G hg s hI e).sum_repr
    (relativePointFramedYSquare G hg s hI e)
  rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)] at h
  refine h.symm.trans ?_
  rw [relativePointMonomialSixBasis_YSquare_last, one_smul,
    relativePointMonomialSixBasis_new]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [relativePointMonomialSixBasis_old]
  rfl

/-- The cubic defect is an actual order-five pole section included by the original map. -/
theorem relativePointCubicDefect :
    relativePointFramedYSquare G hg s hI e - relativePointFramedCube G hg s hI e =
      divisorPowerRingStep G.hom.appTop.hom hI 5
        (∑ i, relativePointCubicCoefficients G hg s hI e i •
          relativePointMonomialFiveBasis G hg s hI e i) := by
  rw [relativePointCubicRelation, add_sub_cancel_right, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_smul (divisorPowerRingStep G.hom.appTop.hom hI 5) _ _).symm

/-- The constructed five coefficients are uniquely determined by the actual cubic defect. -/
theorem relativePointCubicCoefficients_unique
    (c : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → Γ(S, ⊤))
    (hc : relativePointFramedYSquare G hg s hI e - relativePointFramedCube G hg s hI e =
      divisorPowerRingStep G.hom.appTop.hom hI 5
        (∑ i, c i • relativePointMonomialFiveBasis G hg s hI e i)) :
    c = relativePointCubicCoefficients G hg s hI e := by
  have h := divisorPowerRingStep_injective G.hom.appTop.hom hI 5
    (hc.symm.trans (relativePointCubicDefect G hg s hI e))
  apply (relativePointMonomialFiveBasis G hg s hI e).equivFun.symm.injective
  simpa only [Module.Basis.equivFun_symm_apply] using h

end FLT.Mazur.FCurve
