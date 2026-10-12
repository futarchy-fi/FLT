/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneProjectiveSections
public import FLT.Mazur.RelativeGenusOneComplementEquation

/-!
# The homogeneous equation on the original total space

The original degree-three coordinate sections satisfy the degree-nine
Weierstrass relation as actual global sections, including along the marking.
Faithfulness of Cartier-complement evaluation proves the global identity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "X" => relativePointProjectiveX G hg s hI e
local notation "Y" => relativePointProjectiveY G hg s hI e
local notation "Z" => relativePointProjectiveZ G s hI
local notation "W" => relativePointWeierstrassCurve G hg s hI e

/-- The degree-three X section has the same original complement coordinate. -/
theorem relativePointProjectiveX_function : divisorComplementFunction hI 3 (X) =
    relativePointComplementX G hg s hI e := by
  have h := relativePoleFunction_step G.hom s.left hI 2
    (relativePointFramedLift G hg s hI e 1 (by decide))
  unfold relativePoleFunction at h
  unfold relativePointProjectiveX relativePointComplementX relativePoleFunction
  exact h

/-- The degree-three Y section retains the original order-three function. -/
theorem relativePointProjectiveY_function : divisorComplementFunction hI 3 (Y) =
    relativePointComplementY G hg s hI e := by
  unfold relativePointProjectiveY relativePointComplementY relativePoleFunction
  rfl

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom] in
/-- The canonical cube is the constant one in the original affine chart. -/
theorem relativePointProjectiveZ_function : divisorComplementFunction hI 3 (Z) = 1 :=
  divisorComplementFunction_power hI 3

/-- Multiply three original degree-three sections into the actual degree-nine line. -/
def relativePointCubicProduct (a b c : Γ(tensorPower (L) 3, ⊤)) :
    Γ(tensorPower (L) 9, ⊤) :=
  SectionGradedMultiplication.mul (L) ⊤ 6 3
    (SectionGradedMultiplication.mul (L) ⊤ 3 3 a b) c

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom] in
/-- The degree-nine product restricts to multiplication of the three original functions. -/
theorem relativePointCubicProduct_function (a b c : Γ(tensorPower (L) 3, ⊤)) :
    divisorComplementFunction hI 9 (relativePointCubicProduct G s hI a b c) =
      divisorComplementFunction hI 3 a * divisorComplementFunction hI 3 b *
        divisorComplementFunction hI 3 c := by
  unfold relativePointCubicProduct
  rw [divisorComplementFunction_mul hI 6 3, divisorComplementFunction_mul hI 3 3]

local notation "P" => relativePointCubicProduct G s hI
local notation "A" => G.hom.appTop

/-- The homogeneous Weierstrass identity holds globally on the original varying family. -/
theorem relativePointProjectiveSections_equation :
    P (Y) (Y) (Z) + A (W).a₁ • P (X) (Y) (Z) + A (W).a₃ • P (Y) (Z) (Z) =
      P (X) (X) (X) + A (W).a₂ • P (X) (X) (Z) + A (W).a₄ • P (X) (Z) (Z) +
        A (W).a₆ • P (Z) (Z) (Z) := by
  apply divisorComplementFunction_injective hI 9
  simp only [divisorComplementFunction_add, divisorComplementFunction_smul,
    relativePointCubicProduct_function, relativePointProjectiveX_function,
    relativePointProjectiveY_function, relativePointProjectiveZ_function, mul_one]
  have he := relativePointWeierstrass_equation G hg s hI e
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, pow_two, pow_succ,
    relativePointComplementBaseMap, RingHom.comp_apply, mul_assoc, pow_zero, mul_one,
    one_mul] using he

end FLT.Mazur.FCurve
