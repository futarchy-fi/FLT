/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointComplementMonomials
public import FLT.Mazur.PolygonCompletePointIntegralCubic
public import FLT.Mazur.WeightedPoleCubicNormalization

/-!
# The integral Weierstrass equation on the original Cartier complement

The actual integral cubic relation evaluates to an equation of the original
functions. Its five coefficients define a Weierstrass curve over the complete base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor relativePoleFunction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "x" => completePointComplementX K n h i
local notation "y" => completePointComplementY K n h i
local notation "φ" => completePointComplementBaseMap K n h i
local notation "c" => completePointCubicCoefficients K n h i

/-- Evaluation of the original section relation on the actual divisor complement. -/
theorem completePointComplement_cubicSum :
    y ^ 2 = (∑ j, φ (c j) * completePointLowerMonomial x y j) + x ^ 3 := by
  have he := congrArg (relativePoleFunctionAddHom f s hI 6)
    (completePointCubicRelation K n h i)
  rw [map_add, map_sum] at he
  change relativePoleFunction f s hI 6 (completePointPoleYSquare K n h i) =
    (∑ j, relativePoleFunction f s hI 6
      (c j • divisorPowerRingStep (f).appTop.hom hI 5
        (completePointFiveMonomialBasis K n h i j))) +
      relativePoleFunction f s hI 6 (completePointPoleCube K n h i) at he
  simp only [relativePoleFunction_smul, relativePoleFunction_step,
    completePointComplement_fiveBasis, completePointComplement_ySquare,
    completePointComplement_cube] at he
  exact he

/-- Reindex the five constructed coefficients and append the proved unit cube coefficient. -/
def completePointWeierstrassCoefficients : Fin 6 → Γ(Spec (.of (PowerSeries K)), ⊤) :=
  ![c (Sum.inl (Sum.inl (Sum.inl (Sum.inl ())))),
    c (Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))),
    c (Sum.inl (Sum.inl (Sum.inr ()))), c (Sum.inl (Sum.inr ())), c (Sum.inr ()), 1]

/-- The six-term cubic relation has leading coefficient one over the actual base ring. -/
theorem completePointComplement_cubic :
    let a := completePointWeierstrassCoefficients K n h i
    y ^ 2 = φ (a 0) + φ (a 1) * x + φ (a 2) * y +
      φ (a 3) * x ^ 2 + φ (a 4) * (x * y) + φ (a 5) * x ^ 3 := by
  have he := completePointComplement_cubicSum K n h i
  simpa only [completePointWeierstrassCoefficients, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Fintype.sum_sum_type,
    Fintype.sum_unique, completePointLowerMonomial, completePointLowMonomial,
    Sum.elim_inl, Sum.elim_inr, mul_one, map_one, one_mul] using he

/-- The actual relative Weierstrass curve from the original five cubic coefficients. -/
def completePointWeierstrassCurve : WeierstrassCurve Γ(Spec (.of (PowerSeries K)), ⊤) :=
  WeightedPoleMonomials.cubicCurve (completePointWeierstrassCoefficients K n h i)

/-- The original complement coordinates satisfy the constructed relative Weierstrass equation. -/
theorem completePointWeierstrass_equation :
    ((completePointWeierstrassCurve K n h i).map φ).toAffine.Equation x y := by
  have he := WeightedPoleMonomials.cubicCurve_equation φ
    (completePointWeierstrassCoefficients K n h i) x y
    (completePointComplement_cubic K n h i)
  simpa only [completePointWeierstrassCurve, completePointWeierstrassCoefficients,
    Matrix.cons_val_succ,
    Matrix.cons_val, Matrix.cons_val_zero, map_one, one_mul] using he

end FLT.Mazur.PolygonInfinitesimalStages
