/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingComplementMonomials
public import FLT.Mazur.GeneralizedCurveMarkingCubicRelation
public import FLT.Mazur.WeightedPoleCubicNormalization

/-!
# The relative cubic as an equation of actual complement functions

Evaluate the constructed original H0 relation and retain its five base-ring
coefficients. The resulting Weierstrass equation uses the unscaled coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionPoleMultiplicativeCoordinates Scheme.Modules.pullback
  relativePoleFunction smoothMarkingMonomialFourBasis smoothMarkingMonomialFiveBasis
  smoothMarkingMonomialSixBasis smoothMarkingFramedThreeBasis

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The structure morphism is proper for the original family. -/
local instance generalizedCurveMarkingComplementEquationProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "x" => smoothMarkingComplementX E s e
local notation "y" => smoothMarkingComplementY E s e
local notation "φ" => smoothMarkingComplementBaseMap E s
local notation "c" => smoothMarkingCubicCoefficients E s e

/-- Evaluation of the original section relation on the actual divisor complement. -/
theorem smoothMarkingComplement_cubicSum :
    y ^ 2 = (∑ i, φ (c i) * smoothMarkingLowerMonomial x y i) + x ^ 3 := by
  have h := congrArg (relativePoleFunctionAddHom E.curve.hom (t).left (hI) 6)
    (smoothMarkingCubicRelation E s e)
  rw [map_add, map_sum] at h
  change relativePoleFunction E.curve.hom (t).left (hI) 6 (smoothMarkingFramedYSquare E s e) =
    (∑ i, relativePoleFunction E.curve.hom (t).left (hI) 6
      (c i • divisorPowerRingStep E.curve.hom.appTop.hom (hI) 5
        (smoothMarkingMonomialFiveBasis E s e i))) +
      relativePoleFunction E.curve.hom (t).left (hI) 6 (smoothMarkingFramedCube E s e) at h
  simp only [relativePoleFunction_smul, relativePoleFunction_step,
    smoothMarkingComplement_fiveBasis, smoothMarkingComplement_ySquare,
    smoothMarkingComplement_cube] at h
  exact h

/-- Reindex the five constructed coefficients and append the proved unit cube coefficient. -/
def smoothMarkingWeierstrassCoefficients : Fin 6 → Γ(S, ⊤) :=
  ![c (Sum.inl (Sum.inl (Sum.inl (Sum.inl ())))),
    c (Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))),
    c (Sum.inl (Sum.inl (Sum.inr ()))), c (Sum.inl (Sum.inr ())), c (Sum.inr ()), 1]

/-- The six-term cubic relation has leading coefficient one over the actual base ring. -/
theorem smoothMarkingComplement_cubic :
    let a := smoothMarkingWeierstrassCoefficients E s e
    y ^ 2 = φ (a 0) + φ (a 1) * x + φ (a 2) * y +
      φ (a 3) * x ^ 2 + φ (a 4) * (x * y) + φ (a 5) * x ^ 3 := by
  have h := smoothMarkingComplement_cubicSum E s e
  simpa only [smoothMarkingWeierstrassCoefficients, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Fintype.sum_sum_type,
    Fintype.sum_unique, smoothMarkingLowerMonomial, smoothMarkingLowMonomial,
    Sum.elim_inl, Sum.elim_inr, mul_one, map_one, one_mul] using h

/-- The actual relative Weierstrass curve from the original five cubic coefficients. -/
def smoothMarkingWeierstrassCurve : WeierstrassCurve Γ(S, ⊤) :=
  WeightedPoleMonomials.cubicCurve (smoothMarkingWeierstrassCoefficients E s e)

/-- The original complement coordinates satisfy the constructed relative Weierstrass equation. -/
theorem smoothMarkingWeierstrass_equation :
    ((smoothMarkingWeierstrassCurve E s e).map φ).toAffine.Equation x y := by
  have h := WeightedPoleMonomials.cubicCurve_equation φ
    (smoothMarkingWeierstrassCoefficients E s e) x y
    (smoothMarkingComplement_cubic E s e)
  simpa only [smoothMarkingWeierstrassCurve, smoothMarkingWeierstrassCoefficients,
    Matrix.cons_val_succ,
    Matrix.cons_val, Matrix.cons_val_zero, map_one, one_mul] using h

end FLT.Mazur.GeneralizedEllipticCurve
