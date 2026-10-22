/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFramedProducts
public import FLT.Mazur.SectionPoleSpecifiedBasis

/-!
# The order-six monomial basis on original singular families

Extend the normalized order-three basis successively by the actual square,
mixed product and cube. The old vectors use the original divisor inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionPoleMultiplicativeCoordinates Scheme.Modules.pullback

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The structure morphism is proper for the original family. -/
local instance generalizedCurveMarkingMonomialBasisProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The common-frame basis through order three. -/
def smoothMarkingFramedThreeBasis : Basis ((Unit ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
    (ModuleRingH E.curve.hom.appTop.hom (tensorPower (divisorLineBundle (t).left.ker (hI)) 3) 0) :=
  smoothMarkingThreeBasis E s
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e 2)
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e 3)

/-- The first vector retains the original canonical degree-one section and both inclusions. -/
theorem smoothMarkingFramedThreeBasis_one :
    smoothMarkingFramedThreeBasis E s e (Sum.inl (Sum.inl ())) =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 2
        (divisorPowerRingStep E.curve.hom.appTop.hom (hI) 1 (smoothMarkingOneBasis E s ())) := by
  rw [smoothMarkingFramedThreeBasis, smoothMarkingThreeBasis_old]
  congr 1
  let _ : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) 1) 1) :=
    smoothMarkingPower_relative_acyclic E s 1 (by decide) 0
  exact sectionPoleAdaptedBasis_old E.curve.hom (t).left (t).w (hI) 1 _ _ ()

/-- The second vector is the included actual order-two lift. -/
theorem smoothMarkingFramedThreeBasis_x :
    smoothMarkingFramedThreeBasis E s e (Sum.inl (Sum.inr ())) =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 2
        (smoothMarkingFramedLift E s e 1 (by decide)) := by
  rw [smoothMarkingFramedThreeBasis, smoothMarkingThreeBasis_old, smoothMarkingTwoBasis_new]
  rfl

/-- The third vector is the actual order-three lift. -/
theorem smoothMarkingFramedThreeBasis_y :
    smoothMarkingFramedThreeBasis E s e (Sum.inr ()) =
      smoothMarkingFramedLift E s e 2 (by decide) :=
  smoothMarkingThreeBasis_new E s _ _

/-- The actual square extends the low-pole basis through order four. -/
def smoothMarkingMonomialFourBasis : Basis (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
    (ModuleRingH E.curve.hom.appTop.hom (tensorPower (divisorLineBundle (t).left.ker (hI)) 4) 0) :=
  sectionPoleSpecifiedBasis E.curve.hom (t).left (t).w (hI) 3
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e 4)
    (smoothMarkingFramedThreeBasis E s e) (smoothMarkingFramedSquare E s e)
    ((sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w 3 _).symm.trans
      (smoothMarkingFramedSquare_coefficient E s e))

/-- The actual mixed product extends the same basis through order five. -/
def smoothMarkingMonomialFiveBasis : Basis ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
    (ModuleRingH E.curve.hom.appTop.hom (tensorPower (divisorLineBundle (t).left.ker (hI)) 5) 0) :=
  sectionPoleSpecifiedBasis E.curve.hom (t).left (t).w (hI) 4
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e 5)
    (smoothMarkingMonomialFourBasis E s e) (smoothMarkingFramedMixed E s e)
    ((sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w 4 _).symm.trans
      (smoothMarkingFramedMixed_coefficient E s e))

/-- The actual cube completes the compatible six-vector basis in degree six. -/
def smoothMarkingMonomialSixBasis :
    Basis (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
      (ModuleRingH E.curve.hom.appTop.hom
        (tensorPower (divisorLineBundle (t).left.ker (hI)) 6) 0) :=
  sectionPoleSpecifiedBasis E.curve.hom (t).left (t).w (hI) 5
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e 6)
    (smoothMarkingMonomialFiveBasis E s e) (smoothMarkingFramedCube E s e)
    ((sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w 5 _).symm.trans
      (smoothMarkingFramedCube_coefficient E s e))

/-- The new order-four vector is precisely the actual square. -/
theorem smoothMarkingMonomialFourBasis_new :
    smoothMarkingMonomialFourBasis E s e (Sum.inr ()) =
      smoothMarkingFramedSquare E s e :=
  sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

/-- The new order-five vector is precisely the actual mixed product. -/
theorem smoothMarkingMonomialFiveBasis_new :
    smoothMarkingMonomialFiveBasis E s e (Sum.inr ()) =
      smoothMarkingFramedMixed E s e :=
  sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

/-- The final vector is precisely the cube of the original order-two lift. -/
theorem smoothMarkingMonomialSixBasis_new :
    smoothMarkingMonomialSixBasis E s e (Sum.inr ()) =
      smoothMarkingFramedCube E s e :=
  sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

/-- The order-four basis retains the original order-three vectors. -/
theorem smoothMarkingMonomialFourBasis_old (i : (Unit ⊕ Unit) ⊕ Unit) :
    smoothMarkingMonomialFourBasis E s e (Sum.inl i) =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 3 (smoothMarkingFramedThreeBasis E s e i) :=
  sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The order-five basis retains the original order-four vectors. -/
theorem smoothMarkingMonomialFiveBasis_old (i : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    smoothMarkingMonomialFiveBasis E s e (Sum.inl i) =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 4 (smoothMarkingMonomialFourBasis E s e i) :=
  sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The order-six basis retains the original order-five vectors. -/
theorem smoothMarkingMonomialSixBasis_old (i : (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    smoothMarkingMonomialSixBasis E s e (Sum.inl i) =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 5 (smoothMarkingMonomialFiveBasis E s e i) :=
  sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The cube coefficient of any section is its original leading coefficient. -/
theorem smoothMarkingMonomialSixBasis_repr_last
    (z : ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) 6) 0) :
    (smoothMarkingMonomialSixBasis E s e).repr z (Sum.inr ()) =
      sectionPoleCoefficient (t).left (hI) e 6 (moduleH0Equiv _ z) :=
  (sectionPoleSpecifiedBasis_repr_new _ _ _ _ _ _ _ _ _ z).trans
    (sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w 5 z).symm

/-- The square of the order-three lift has cube coefficient exactly one. -/
theorem smoothMarkingMonomialSixBasis_YSquare_last :
    (smoothMarkingMonomialSixBasis E s e).repr
      (smoothMarkingFramedYSquare E s e) (Sum.inr ()) = 1 := by
  rw [smoothMarkingMonomialSixBasis_repr_last, smoothMarkingFramedYSquare_coefficient]

end FLT.Mazur.GeneralizedEllipticCurve
