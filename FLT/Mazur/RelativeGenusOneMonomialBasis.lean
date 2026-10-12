/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneFramedProducts
public import FLT.Mazur.SectionPoleSpecifiedBasis

/-!
# The compatible order-six basis from actual pole products

Extend the normalized order-three basis successively by the actual square,
mixed product and cube. The old vectors use the original divisor inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
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

/-- The common-frame basis through order three. -/
def relativePointFramedThreeBasis : Basis ((Unit ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
    (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 3) 0) :=
  relativePointThreeBasis G hg s hI
    (sectionPoleMultiplicativeCoordinates s.left hI e 2)
    (sectionPoleMultiplicativeCoordinates s.left hI e 3)

/-- The first vector retains the original canonical degree-one section and both inclusions. -/
theorem relativePointFramedThreeBasis_one :
    relativePointFramedThreeBasis G hg s hI e (Sum.inl (Sum.inl ())) =
      divisorPowerRingStep G.hom.appTop.hom hI 2
        (divisorPowerRingStep G.hom.appTop.hom hI 1 (relativePointOneBasis G hg s hI ())) := by
  rw [relativePointFramedThreeBasis, relativePointThreeBasis_old]
  congr 1
  let _ := relative_pointPower_acyclic G hg s hI 1 (by decide) 0
  exact sectionPoleAdaptedBasis_old G.hom s.left s.w hI 1 _ _ ()

/-- The second vector is the included actual order-two lift. -/
theorem relativePointFramedThreeBasis_x :
    relativePointFramedThreeBasis G hg s hI e (Sum.inl (Sum.inr ())) =
      divisorPowerRingStep G.hom.appTop.hom hI 2
        (relativePointFramedLift G hg s hI e 1 (by decide)) := by
  rw [relativePointFramedThreeBasis, relativePointThreeBasis_old, relativePointTwoBasis_new]
  rfl

/-- The third vector is the actual order-three lift. -/
theorem relativePointFramedThreeBasis_y :
    relativePointFramedThreeBasis G hg s hI e (Sum.inr ()) =
      relativePointFramedLift G hg s hI e 2 (by decide) :=
  relativePointThreeBasis_new G hg s hI _ _

/-- The actual square extends the low-pole basis through order four. -/
def relativePointMonomialFourBasis : Basis (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
    (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 4) 0) :=
  sectionPoleSpecifiedBasis G.hom s.left s.w hI 3
    (sectionPoleMultiplicativeCoordinates s.left hI e 4)
    (relativePointFramedThreeBasis G hg s hI e) (relativePointFramedSquare G hg s hI e)
    ((sectionPoleCoefficient_leading s.left hI e G.hom s.w 3 _).symm.trans
      (relativePointFramedSquare_coefficient G hg s hI e))

/-- The actual mixed product extends the same basis through order five. -/
def relativePointMonomialFiveBasis : Basis ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
    (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 5) 0) :=
  sectionPoleSpecifiedBasis G.hom s.left s.w hI 4
    (sectionPoleMultiplicativeCoordinates s.left hI e 5)
    (relativePointMonomialFourBasis G hg s hI e) (relativePointFramedMixed G hg s hI e)
    ((sectionPoleCoefficient_leading s.left hI e G.hom s.w 4 _).symm.trans
      (relativePointFramedMixed_coefficient G hg s hI e))

/-- The actual cube completes the compatible six-vector basis in degree six. -/
def relativePointMonomialSixBasis :
    Basis (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
      (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 6) 0) :=
  sectionPoleSpecifiedBasis G.hom s.left s.w hI 5
    (sectionPoleMultiplicativeCoordinates s.left hI e 6)
    (relativePointMonomialFiveBasis G hg s hI e) (relativePointFramedCube G hg s hI e)
    ((sectionPoleCoefficient_leading s.left hI e G.hom s.w 5 _).symm.trans
      (relativePointFramedCube_coefficient G hg s hI e))

/-- The new order-four vector is precisely the actual square. -/
theorem relativePointMonomialFourBasis_new :
    relativePointMonomialFourBasis G hg s hI e (Sum.inr ()) =
      relativePointFramedSquare G hg s hI e :=
  sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

/-- The new order-five vector is precisely the actual mixed product. -/
theorem relativePointMonomialFiveBasis_new :
    relativePointMonomialFiveBasis G hg s hI e (Sum.inr ()) =
      relativePointFramedMixed G hg s hI e :=
  sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

/-- The final vector is precisely the cube of the original order-two lift. -/
theorem relativePointMonomialSixBasis_new :
    relativePointMonomialSixBasis G hg s hI e (Sum.inr ()) =
      relativePointFramedCube G hg s hI e :=
  sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

/-- The order-four basis retains the original order-three vectors. -/
theorem relativePointMonomialFourBasis_old (i : (Unit ⊕ Unit) ⊕ Unit) :
    relativePointMonomialFourBasis G hg s hI e (Sum.inl i) =
      divisorPowerRingStep G.hom.appTop.hom hI 3 (relativePointFramedThreeBasis G hg s hI e i) :=
  sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The order-five basis retains the original order-four vectors. -/
theorem relativePointMonomialFiveBasis_old (i : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePointMonomialFiveBasis G hg s hI e (Sum.inl i) =
      divisorPowerRingStep G.hom.appTop.hom hI 4 (relativePointMonomialFourBasis G hg s hI e i) :=
  sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The order-six basis retains the original order-five vectors. -/
theorem relativePointMonomialSixBasis_old (i : (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePointMonomialSixBasis G hg s hI e (Sum.inl i) =
      divisorPowerRingStep G.hom.appTop.hom hI 5 (relativePointMonomialFiveBasis G hg s hI e i) :=
  sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The cube coefficient of any section is its original leading coefficient. -/
theorem relativePointMonomialSixBasis_repr_last
    (z : ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) 6) 0) :
    (relativePointMonomialSixBasis G hg s hI e).repr z (Sum.inr ()) =
      sectionPoleCoefficient s.left hI e 6 (moduleH0Equiv _ z) :=
  (sectionPoleSpecifiedBasis_repr_new _ _ _ _ _ _ _ _ _ z).trans
    (sectionPoleCoefficient_leading s.left hI e G.hom s.w 5 z).symm

/-- The square of the order-three lift has cube coefficient exactly one. -/
theorem relativePointMonomialSixBasis_YSquare_last :
    (relativePointMonomialSixBasis G hg s hI e).repr
      (relativePointFramedYSquare G hg s hI e) (Sum.inr ()) = 1 := by
  rw [relativePointMonomialSixBasis_repr_last, relativePointFramedYSquare_coefficient]

end FLT.Mazur.FCurve
