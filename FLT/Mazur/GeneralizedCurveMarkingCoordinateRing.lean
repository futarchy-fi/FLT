/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCoordinateSurjective
public import FLT.Mazur.GeneralizedCurveMarkingNormalMonomials
public import FLT.Mazur.WeierstrassAffineEvaluationInjective

/-!
# The relative Weierstrass coordinate ring of the original complement

Independent actual monomials make the original evaluation injective, while
pole exhaustion makes it surjective. The ring isomorphism retains the base scalars.
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
local instance generalizedCurveMarkingCoordinateRingProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "W" => smoothMarkingWeierstrassCurve E s e

/-- The original relative coordinate evaluation is injective over the actual base ring. -/
theorem smoothMarkingCoordinateEvaluation_injective :
    Function.Injective (smoothMarkingCoordinateEvaluation E s e) :=
  WeierstrassAffineEquationEvaluation.evaluation_injective (W)
    (smoothMarkingComplementBaseMap E s) (smoothMarkingComplementX E s e)
    (smoothMarkingComplementY E s e) (smoothMarkingWeierstrass_equation E s e)
    (smoothMarkingNormalMonomials_independent E s e)

/-- The constructed relative cubic ring is the entire original complement function ring. -/
def smoothMarkingCoordinateRingEquiv : (W).toAffine.CoordinateRing ≃+*
    Γ(Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl, ⊤) :=
  RingEquiv.ofBijective (smoothMarkingCoordinateEvaluation E s e)
    ⟨smoothMarkingCoordinateEvaluation_injective E s e,
      smoothMarkingCoordinateEvaluation_surjective E s e⟩

/-- The original base ring map is retained by the constructed ring isomorphism. -/
theorem smoothMarkingCoordinateRingEquiv_scalar (a : Γ(S, ⊤)) :
    smoothMarkingCoordinateRingEquiv E s e
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing a) =
        smoothMarkingComplementBaseMap E s a :=
  smoothMarkingCoordinateEvaluation_scalar E s e a

/-- The ring isomorphism retains the original order-two function. -/
theorem smoothMarkingCoordinateRingEquiv_x :
    smoothMarkingCoordinateRingEquiv E s e
      (algebraMap (Polynomial Γ(S, ⊤)) (W).toAffine.CoordinateRing Polynomial.X) =
        smoothMarkingComplementX E s e :=
  smoothMarkingCoordinateEvaluation_x E s e

/-- The ring isomorphism retains the original order-three function. -/
theorem smoothMarkingCoordinateRingEquiv_y :
    smoothMarkingCoordinateRingEquiv E s e (AdjoinRoot.root (W).toAffine.polynomial) =
      smoothMarkingComplementY E s e :=
  smoothMarkingCoordinateEvaluation_y E s e

end FLT.Mazur.GeneralizedEllipticCurve
