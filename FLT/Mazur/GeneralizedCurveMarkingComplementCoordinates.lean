/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFramedProducts
public import FLT.Mazur.RelativePoleComplementFunctions
public import FLT.Mazur.DivisorComplementCanonicalUnitor

/-!
# Original relative coordinates on the divisor complement

The normalized low-pole lifts give actual regular functions x and y. Their
original tensor products represent the usual powers and mixed product.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionPoleMultiplicativeCoordinates Scheme.Modules.pullback
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The structure morphism is proper for the original family. -/
local instance generalizedCurveMarkingComplementCoordinatesProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The base scalars on the actual complement, through its original structure map. -/
def smoothMarkingComplementBaseMap :
    Γ(S, ⊤) →+* Γ(Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl, ⊤) :=
  (Scheme.Opens.ι (X := E.curve.left) (t).left.ker.support.compl).appTop.hom.comp
    E.curve.hom.appTop.hom

/-- The order-two coordinate is the function of the original normalized lift. -/
def smoothMarkingComplementX :
    Γ(Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl, ⊤) :=
  relativePoleFunction E.curve.hom (t).left (hI) 2
    (smoothMarkingFramedLift E s e 1 (by decide))

/-- The order-three coordinate is the function of the original normalized lift. -/
def smoothMarkingComplementY :
    Γ(Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl, ⊤) :=
  relativePoleFunction E.curve.hom (t).left (hI) 3
    (smoothMarkingFramedLift E s e 2 (by decide))

/-- The canonical degree-one vector represents one on the actual complement. -/
theorem smoothMarkingComplement_oneBasis :
    relativePoleFunction E.curve.hom (t).left (hI) 1
      (smoothMarkingOneBasis E s ()) = 1 := by
  unfold relativePoleFunction
  exact divisorComplementFunction_one_of_unitor (hI) _ (smoothMarkingOneBasis_section E s)

/-- The actual order-four product represents x squared. -/
theorem smoothMarkingComplement_square :
    relativePoleFunction E.curve.hom (t).left (hI) 4 (smoothMarkingFramedSquare E s e) =
      smoothMarkingComplementX E s e ^ 2 := by
  exact (relativePoleFunction_product E.curve.hom (t).left (hI) 2 2 _ _).trans
    (pow_two (smoothMarkingComplementX E s e)).symm

/-- The actual order-five product represents xy. -/
theorem smoothMarkingComplement_mixed :
    relativePoleFunction E.curve.hom (t).left (hI) 5 (smoothMarkingFramedMixed E s e) =
      smoothMarkingComplementX E s e * smoothMarkingComplementY E s e := by
  exact relativePoleFunction_product E.curve.hom (t).left (hI) 2 3 _ _

/-- The original order-six cube represents x cubed. -/
theorem smoothMarkingComplement_cube :
    relativePoleFunction E.curve.hom (t).left (hI) 6 (smoothMarkingFramedCube E s e) =
      smoothMarkingComplementX E s e ^ 3 := by
  apply (relativePoleFunction_product E.curve.hom (t).left (hI) 4 2 _ _).trans
  rw [smoothMarkingComplement_square]
  exact (pow_succ (smoothMarkingComplementX E s e) 2).symm

/-- The original order-six square represents y squared. -/
theorem smoothMarkingComplement_ySquare :
    relativePoleFunction E.curve.hom (t).left (hI) 6 (smoothMarkingFramedYSquare E s e) =
      smoothMarkingComplementY E s e ^ 2 := by
  exact (relativePoleFunction_product E.curve.hom (t).left (hI) 3 3 _ _).trans
    (pow_two (smoothMarkingComplementY E s e)).symm

end FLT.Mazur.GeneralizedEllipticCurve
