/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingComplementEquation
public import FLT.Mazur.WeierstrassAffineEquationEvaluation

/-!
# The actual relative morphism to the affine cubic

The constructed equation induces an original coordinate-ring evaluation and
a scheme morphism from the divisor complement, with its base map retained.
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
local instance generalizedCurveMarkingAffineCubicMorphismProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "x" => smoothMarkingComplementX E s e
local notation "y" => smoothMarkingComplementY E s e
local notation "φ" => smoothMarkingComplementBaseMap E s
local notation "W" => smoothMarkingWeierstrassCurve E s e

/-- Evaluate the constructed affine coordinate ring in the original complement functions. -/
def smoothMarkingCoordinateEvaluation : (W).toAffine.CoordinateRing →+*
    Γ(Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl, ⊤) :=
  WeierstrassAffineEquationEvaluation.evaluation W φ x y
    (smoothMarkingWeierstrass_equation E s e)

/-- Evaluation retains the original coefficient map. -/
theorem smoothMarkingCoordinateEvaluation_scalar (r : Γ(S, ⊤)) :
    smoothMarkingCoordinateEvaluation E s e
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing r) = φ r :=
  WeierstrassAffineEquationEvaluation.evaluation_scalar W φ x y _ r

/-- The coordinate-ring map is over the actual base ring. -/
theorem smoothMarkingCoordinateEvaluation_comp_scalar :
    (smoothMarkingCoordinateEvaluation E s e).comp
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing) = φ :=
  RingHom.ext (smoothMarkingCoordinateEvaluation_scalar E s e)

/-- The first universal coordinate evaluates to the original order-two function. -/
theorem smoothMarkingCoordinateEvaluation_x :
    smoothMarkingCoordinateEvaluation E s e
      (algebraMap (Polynomial Γ(S, ⊤)) (W).toAffine.CoordinateRing Polynomial.X) = x :=
  WeierstrassAffineEquationEvaluation.evaluation_x W φ x y _

/-- The second universal coordinate evaluates to the original order-three function. -/
theorem smoothMarkingCoordinateEvaluation_y :
    smoothMarkingCoordinateEvaluation E s e (AdjoinRoot.root (W).toAffine.polynomial) = y :=
  WeierstrassAffineEquationEvaluation.evaluation_y W φ x y _

/-- The actual scheme morphism defined by the original normalized pole functions. -/
def smoothMarkingToAffineCubic :
    Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl ⟶
      Spec (.of (W).toAffine.CoordinateRing) :=
  (Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (smoothMarkingCoordinateEvaluation E s e))

/-- The scheme morphism has the original structure map to the affine base spectrum. -/
theorem smoothMarkingToAffineCubic_over :
    smoothMarkingToAffineCubic E s e ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing)) =
        (Scheme.Opens.ι (X := E.curve.left) (t).left.ker.support.compl) ≫
          E.curve.hom ≫ S.toSpecΓ := by
  rw [smoothMarkingToAffineCubic, Category.assoc, ← Spec.map_comp]
  change (Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((smoothMarkingCoordinateEvaluation E s e).comp
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing))) = _
  rw [smoothMarkingCoordinateEvaluation_comp_scalar]
  change _ ≫ Spec.map (E.curve.hom.appTop ≫
    (Scheme.Opens.ι (X := E.curve.left) (t).left.ker.support.compl).appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← Scheme.toSpecΓ_naturality]

end FLT.Mazur.GeneralizedEllipticCurve
