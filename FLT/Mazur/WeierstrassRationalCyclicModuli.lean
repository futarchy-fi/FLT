/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassRationalGroupSection
public import FLT.Mazur.RationalCyclicGeneratorChange

/-!
# Classical Weierstrass torsion points give actual ample cyclic moduli points

Apply the geometric subgroup and divisor constructions to the original
projective point in the proved Weierstrass group. Smoothness and geometric
integrality are supplied by the constructed cubic, not additional hypotheses.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup

variable {K : Type} [Field K] (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)
  {n : ℕ} [NeZero n] (P : (W.map (algebraMap K K)).toProjective.Point) (ho : addOrderOf P = n)

/-- The finite closed subgroup constructed from the original classical torsion point. -/
def projectiveRationalCyclicSubgroup : (integralGeneralizedEllipticCurve W hΔ).FiniteSubgroup n :=
  (integralGeneralizedEllipticCurve W hΔ).rationalCyclicSubgroup
    (projectiveRationalGroupSection W hΔ P) ((projectiveRationalGroupSection_order W hΔ P).trans ho)

/-- The classical point's constructed subgroup is etale of the original rank. -/
theorem projectiveRationalCyclicSubgroup_etale :
    Etale (projectiveRationalCyclicSubgroup W hΔ P ho).carrier.hom :=
  ConstantCyclicFiniteEtale.etale K n

/-- Its divisor generator is the prescribed component-one section. -/
def projectiveRationalCyclicGenerator :
    𝟙_ (Over (Spec (.of K))) ⟶ (projectiveRationalCyclicSubgroup W hΔ P ho).carrier :=
  (integralGeneralizedEllipticCurve W hΔ).rationalCyclicGenerator
    (projectiveRationalGroupSection W hΔ P) ((projectiveRationalGroupSection_order W hΔ P).trans ho)

/-- The subgroup inclusion recovers the section constructed from the original point. -/
theorem projectiveRationalCyclicGenerator_inclusion :
    projectiveRationalCyclicGenerator W hΔ P ho ≫
      (projectiveRationalCyclicSubgroup W hΔ P ho).inclusion =
        projectiveRationalGroupSection W hΔ P :=
  (integralGeneralizedEllipticCurve W hΔ).rationalCyclicGenerator_inclusion
    (projectiveRationalGroupSection W hΔ P) ((projectiveRationalGroupSection_order W hΔ P).trans ho)

/-- The classical rational point constructs genuine ample cyclic level data. -/
def projectiveRationalCyclicLevel : ampleCyclicLevels (Spec (.of K)) n := by
  let E := integralGeneralizedEllipticCurve W hΔ
  let _ : SmoothOfRelativeDimension 1 E.curve.hom := integralCurveStructure_smooth_dimension W hΔ
  let _ : GeometricallyIntegral E.curve.hom :=
    inferInstanceAs (GeometricallyIntegral (integralCurveStructure W))
  exact E.rationalCyclicLevel (projectiveRationalGroupSection W hΔ P)
    ((projectiveRationalGroupSection_order W hΔ P).trans ho)

/-- The point's actual isomorphism class in the ample cyclic moduli presheaf. -/
def projectiveRationalCyclicModuliPoint : ampleCyclicClasses (Spec (.of K)) n :=
  Quotient.mk _ (projectiveRationalCyclicLevel W hΔ P ho)

/-- The moduli class forgets to the original point's constructed finite etale subgroup. -/
theorem projectiveRationalCyclicModuliPoint_forget :
    ampleCyclicClassesForget (Spec (.of K)) n (projectiveRationalCyclicModuliPoint W hΔ P ho) =
      Quotient.mk (compatibleIsoSetoid (Spec (.of K)) n)
        ⟨integralGeneralizedEllipticCurve W hΔ, projectiveRationalCyclicSubgroup W hΔ P ho⟩ := rfl

/-- Coprime changes of the classical generator preserve its actual moduli point. -/
theorem projectiveRationalCyclicModuliPoint_nsmul (k : ℕ) (hk : k.Coprime n)
    (hok : addOrderOf (k • P) = n) :
    projectiveRationalCyclicModuliPoint W hΔ (k • P) hok =
      projectiveRationalCyclicModuliPoint W hΔ P ho := by
  let E := integralGeneralizedEllipticCurve W hΔ
  let _ : SmoothOfRelativeDimension 1 E.curve.hom := integralCurveStructure_smooth_dimension W hΔ
  let _ : GeometricallyIntegral E.curve.hom :=
    inferInstanceAs (GeometricallyIntegral (integralCurveStructure W))
  have hP := (projectiveRationalGroupSection_order W hΔ P).trans ho
  have hs : projectiveRationalGroupSection W hΔ (k • P) =
      projectiveRationalGroupSection W hΔ P ^ k :=
    congrArg Additive.toMul ((projectiveRationalGroupSectionAddHom W hΔ).map_nsmul k P)
  change E.rationalCyclicModuliPoint (projectiveRationalGroupSection W hΔ (k • P)) _ =
    E.rationalCyclicModuliPoint (projectiveRationalGroupSection W hΔ P) _
  simpa only [hs] using E.rationalCyclicModuliPoint_pow
    (projectiveRationalGroupSection W hΔ P) hP k hk
    (E.rationalCyclicPower_order (projectiveRationalGroupSection W hΔ P) hP k hk)

/-- An affine rational exact-order point supplies the same actual ample cyclic moduli functor. -/
def affineRationalCyclicModuliPoint [DecidableEq K] [W.IsElliptic]
    (Q : (W.map (algebraMap K K)).toAffine.Point) (hQ : addOrderOf Q = n) :
    ampleCyclicClasses (Spec (.of K)) n :=
  projectiveRationalCyclicModuliPoint W W.isUnit_Δ
    ((WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.map (algebraMap K K)).toProjective).symm Q)
    (((WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.map (algebraMap K K)).toProjective).symm.addOrderOf_eq Q).trans hQ)

end FLT.Mazur.WeierstrassIntegralChart
