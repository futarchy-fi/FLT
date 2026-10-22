/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingLowPoles
public import FLT.Mazur.SectionPoleHZeroMultiplication

/-!
# Normalized pole products from a common original frame

The order-two and order-three lifts are normalized in powers of one frame.
Their actual products in degrees four, five and six have leading coefficient one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
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
local instance generalizedCurveMarkingFramedProductsProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The actual lift normalized in the corresponding power of one original frame. -/
def smoothMarkingFramedLift (m : ℕ) (hm : 0 < m) :
    ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) (m + 1)) 0 :=
  smoothMarkingNormalizedLift E s m hm
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e (m + 1))

/-- Every framed lift has coefficient one when restricting the original section. -/
theorem smoothMarkingFramedLift_coefficient (m : ℕ) (hm : 0 < m) :
    sectionPoleCoefficient (t).left (hI) e (m + 1)
      (moduleH0Equiv _ (smoothMarkingFramedLift E s e m hm)) = 1 :=
  (sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w m _).trans
    (smoothMarkingNormalizedLift_leading E s m hm _)

/-- The square of the actual order-two lift, in the original order-four module. -/
def smoothMarkingFramedSquare : ModuleRingH E.curve.hom.appTop.hom
    (tensorPower (divisorLineBundle (t).left.ker (hI)) 4) 0 :=
  sectionPoleHZeroProduct E.curve.hom (t).left (hI) 2 2
    (smoothMarkingFramedLift E s e 1 (by decide))
    (smoothMarkingFramedLift E s e 1 (by decide))

/-- The product of the actual order-two and order-three lifts. -/
def smoothMarkingFramedMixed : ModuleRingH E.curve.hom.appTop.hom
    (tensorPower (divisorLineBundle (t).left.ker (hI)) 5) 0 :=
  sectionPoleHZeroProduct E.curve.hom (t).left (hI) 2 3
    (smoothMarkingFramedLift E s e 1 (by decide))
    (smoothMarkingFramedLift E s e 2 (by decide))

/-- The cube multiplies the actual square by the original order-two lift. -/
def smoothMarkingFramedCube : ModuleRingH E.curve.hom.appTop.hom
    (tensorPower (divisorLineBundle (t).left.ker (hI)) 6) 0 :=
  sectionPoleHZeroProduct E.curve.hom (t).left (hI) 4 2
    (smoothMarkingFramedSquare E s e) (smoothMarkingFramedLift E s e 1 (by decide))

/-- The square of the actual order-three lift lies in the original order-six module. -/
def smoothMarkingFramedYSquare : ModuleRingH E.curve.hom.appTop.hom
    (tensorPower (divisorLineBundle (t).left.ker (hI)) 6) 0 :=
  sectionPoleHZeroProduct E.curve.hom (t).left (hI) 3 3
    (smoothMarkingFramedLift E s e 2 (by decide))
    (smoothMarkingFramedLift E s e 2 (by decide))

/-- The actual square of the order-two lift has unit leading coefficient. -/
theorem smoothMarkingFramedSquare_coefficient :
    sectionPoleCoefficient (t).left (hI) e 4
      (moduleH0Equiv _ (smoothMarkingFramedSquare E s e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient E.curve.hom (t).left (hI) e 2 2 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (smoothMarkingFramedLift_coefficient E s e 1 (by decide))
      (smoothMarkingFramedLift_coefficient E s e 1 (by decide))).trans (one_mul 1))

/-- The mixed product has unit leading coefficient in the same frame. -/
theorem smoothMarkingFramedMixed_coefficient :
    sectionPoleCoefficient (t).left (hI) e 5
      (moduleH0Equiv _ (smoothMarkingFramedMixed E s e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient E.curve.hom (t).left (hI) e 2 3 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (smoothMarkingFramedLift_coefficient E s e 1 (by decide))
      (smoothMarkingFramedLift_coefficient E s e 2 (by decide))).trans (one_mul 1))

/-- The cube of the order-two lift has unit leading coefficient. -/
theorem smoothMarkingFramedCube_coefficient :
    sectionPoleCoefficient (t).left (hI) e 6
      (moduleH0Equiv _ (smoothMarkingFramedCube E s e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient E.curve.hom (t).left (hI) e 4 2 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (smoothMarkingFramedSquare_coefficient E s e)
      (smoothMarkingFramedLift_coefficient E s e 1 (by decide))).trans (one_mul 1))

/-- The square of the order-three lift has the same leading coefficient as the cube. -/
theorem smoothMarkingFramedYSquare_coefficient :
    sectionPoleCoefficient (t).left (hI) e 6
      (moduleH0Equiv _ (smoothMarkingFramedYSquare E s e)) = 1 :=
  (sectionPoleHZeroProduct_coefficient E.curve.hom (t).left (hI) e 3 3 _ _).trans
    ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b)
      (smoothMarkingFramedLift_coefficient E s e 2 (by decide))
      (smoothMarkingFramedLift_coefficient E s e 2 (by decide))).trans (one_mul 1))

end FLT.Mazur.GeneralizedEllipticCurve
