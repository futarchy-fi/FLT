/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneComplementMonomials
public import FLT.Mazur.RelativeGenusOneCubicRelation
public import FLT.Mazur.WeightedPoleCubicNormalization

/-!
# The relative cubic as an equation of actual complement functions

Evaluate the constructed original H0 relation and retain its five base-ring
coefficients. The resulting Weierstrass equation uses the unscaled coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction relativePointMonomialFourBasis relativePointMonomialFiveBasis
  relativePointMonomialSixBasis relativePointFramedThreeBasis

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "x" => relativePointComplementX G hg s hI e
local notation "y" => relativePointComplementY G hg s hI e
local notation "φ" => relativePointComplementBaseMap G s
local notation "c" => relativePointCubicCoefficients G hg s hI e

/-- Evaluation of the original section relation on the actual divisor complement. -/
theorem relativePointComplement_cubicSum :
    y ^ 2 = (∑ i, φ (c i) * relativePointLowerMonomial x y i) + x ^ 3 := by
  have h := congrArg (relativePoleFunctionAddHom G.hom s.left hI 6)
    (relativePointCubicRelation G hg s hI e)
  rw [map_add, map_sum] at h
  change relativePoleFunction G.hom s.left hI 6 (relativePointFramedYSquare G hg s hI e) =
    (∑ i, relativePoleFunction G.hom s.left hI 6
      (c i • divisorPowerRingStep G.hom.appTop.hom hI 5
        (relativePointMonomialFiveBasis G hg s hI e i))) +
      relativePoleFunction G.hom s.left hI 6 (relativePointFramedCube G hg s hI e) at h
  simp only [relativePoleFunction_smul, relativePoleFunction_step,
    relativePointComplement_fiveBasis, relativePointComplement_ySquare,
    relativePointComplement_cube] at h
  exact h

/-- Reindex the five constructed coefficients and append the proved unit cube coefficient. -/
def relativePointWeierstrassCoefficients : Fin 6 → Γ(S, ⊤) :=
  ![c (Sum.inl (Sum.inl (Sum.inl (Sum.inl ())))),
    c (Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))),
    c (Sum.inl (Sum.inl (Sum.inr ()))), c (Sum.inl (Sum.inr ())), c (Sum.inr ()), 1]

/-- The six-term cubic relation has leading coefficient one over the actual base ring. -/
theorem relativePointComplement_cubic :
    let a := relativePointWeierstrassCoefficients G hg s hI e
    y ^ 2 = φ (a 0) + φ (a 1) * x + φ (a 2) * y +
      φ (a 3) * x ^ 2 + φ (a 4) * (x * y) + φ (a 5) * x ^ 3 := by
  have h := relativePointComplement_cubicSum G hg s hI e
  simpa only [relativePointWeierstrassCoefficients, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Fintype.sum_sum_type,
    Fintype.sum_unique, relativePointLowerMonomial, relativePointLowMonomial,
    Sum.elim_inl, Sum.elim_inr, mul_one, map_one, one_mul] using h

/-- The actual relative Weierstrass curve from the original five cubic coefficients. -/
def relativePointWeierstrassCurve : WeierstrassCurve Γ(S, ⊤) :=
  WeightedPoleMonomials.cubicCurve (relativePointWeierstrassCoefficients G hg s hI e)

/-- The original complement coordinates satisfy the constructed relative Weierstrass equation. -/
theorem relativePointWeierstrass_equation :
    ((relativePointWeierstrassCurve G hg s hI e).map φ).toAffine.Equation x y := by
  have h := WeightedPoleMonomials.cubicCurve_equation φ
    (relativePointWeierstrassCoefficients G hg s hI e) x y
    (relativePointComplement_cubic G hg s hI e)
  simpa only [relativePointWeierstrassCurve, relativePointWeierstrassCoefficients,
    Matrix.cons_val_succ,
    Matrix.cons_val, Matrix.cons_val_zero, map_one, one_mul] using h

end FLT.Mazur.FCurve
