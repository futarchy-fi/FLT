/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneLowPoleBasis
public import FLT.Mazur.SectionPoleHZeroMultiplication

/-!
# Normalized pole products from a common original frame

The order-two and order-three lifts are normalized in powers of one frame.
Their actual products in degrees four, five and six have leading coefficient one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

/-- The actual lift normalized in the corresponding power of one original frame. -/
def relativePointFramedLift (m : ℕ) (hm : 0 < m) :
    ModuleRingH G.hom.appTop.hom
      (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 0 :=
  relativePointNormalizedLift G hg s hI m hm
    (sectionPoleMultiplicativeCoordinates s.left hI e (m + 1))

/-- Every framed lift has coefficient one when restricting the original section. -/
theorem relativePointFramedLift_coefficient (m : ℕ) (hm : 0 < m) :
    sectionPoleCoefficient s.left hI e (m + 1)
      (moduleH0Equiv _ (relativePointFramedLift G hg s hI e m hm)) = 1 :=
  (sectionPoleCoefficient_leading s.left hI e G.hom s.w m _).trans
    (relativePointNormalizedLift_leading G hg s hI m hm _)

/-- The square of the actual order-two lift, in the original order-four module. -/
def relativePointFramedSquare : ModuleRingH G.hom.appTop.hom
    (tensorPower (divisorLineBundle s.left.ker hI) 4) 0 :=
  sectionPoleHZeroProduct G.hom s.left hI 2 2
    (relativePointFramedLift G hg s hI e 1 (by decide))
    (relativePointFramedLift G hg s hI e 1 (by decide))

/-- The product of the actual order-two and order-three lifts. -/
def relativePointFramedMixed : ModuleRingH G.hom.appTop.hom
    (tensorPower (divisorLineBundle s.left.ker hI) 5) 0 :=
  sectionPoleHZeroProduct G.hom s.left hI 2 3
    (relativePointFramedLift G hg s hI e 1 (by decide))
    (relativePointFramedLift G hg s hI e 2 (by decide))

/-- The cube multiplies the actual square by the original order-two lift. -/
def relativePointFramedCube : ModuleRingH G.hom.appTop.hom
    (tensorPower (divisorLineBundle s.left.ker hI) 6) 0 :=
  sectionPoleHZeroProduct G.hom s.left hI 4 2
    (relativePointFramedSquare G hg s hI e) (relativePointFramedLift G hg s hI e 1 (by decide))

/-- The square of the actual order-three lift lies in the original order-six module. -/
def relativePointFramedYSquare : ModuleRingH G.hom.appTop.hom
    (tensorPower (divisorLineBundle s.left.ker hI) 6) 0 :=
  sectionPoleHZeroProduct G.hom s.left hI 3 3
    (relativePointFramedLift G hg s hI e 2 (by decide))
    (relativePointFramedLift G hg s hI e 2 (by decide))

/-- The actual square of the order-two lift has unit leading coefficient. -/
theorem relativePointFramedSquare_coefficient :
    sectionPoleCoefficient s.left hI e 4
      (moduleH0Equiv _ (relativePointFramedSquare G hg s hI e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient G.hom s.left hI e 2 2 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (relativePointFramedLift_coefficient G hg s hI e 1 (by decide))
      (relativePointFramedLift_coefficient G hg s hI e 1 (by decide))).trans (one_mul 1))

/-- The mixed product has unit leading coefficient in the same frame. -/
theorem relativePointFramedMixed_coefficient :
    sectionPoleCoefficient s.left hI e 5
      (moduleH0Equiv _ (relativePointFramedMixed G hg s hI e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient G.hom s.left hI e 2 3 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (relativePointFramedLift_coefficient G hg s hI e 1 (by decide))
      (relativePointFramedLift_coefficient G hg s hI e 2 (by decide))).trans (one_mul 1))

/-- The cube of the order-two lift has unit leading coefficient. -/
theorem relativePointFramedCube_coefficient :
    sectionPoleCoefficient s.left hI e 6
      (moduleH0Equiv _ (relativePointFramedCube G hg s hI e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient G.hom s.left hI e 4 2 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (relativePointFramedSquare_coefficient G hg s hI e)
      (relativePointFramedLift_coefficient G hg s hI e 1 (by decide))).trans (one_mul 1))

/-- The square of the order-three lift has the same leading coefficient as the cube. -/
theorem relativePointFramedYSquare_coefficient :
    sectionPoleCoefficient s.left hI e 6
      (moduleH0Equiv _ (relativePointFramedYSquare G hg s hI e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient G.hom s.left hI e 3 3 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (relativePointFramedLift_coefficient G hg s hI e 2 (by decide))
      (relativePointFramedLift_coefficient G hg s hI e 2 (by decide))).trans (one_mul 1))

end FLT.Mazur.FCurve
