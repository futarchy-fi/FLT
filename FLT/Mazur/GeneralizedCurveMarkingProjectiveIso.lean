/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGeometricFiberClosedImmersion
public import FLT.Mazur.GeneralizedCurveMarkingCubicGeometricIso
public import FLT.Mazur.RelativeComparisonFiberIso
public import FLT.Mazur.GeneralizedCurveMarkingCubicFinite
public import FLT.Mazur.GeneralizedCurveMarkingPointedCubic
public import FLT.Mazur.WeierstrassClosedImmersionIso

/-!
# The original relative genus-one curve is its complete pointed cubic

For integral geometric fibers, including singular fibers, the finite original
map has trivial geometric scheme fibers and is a closed immersion.
Its affine chart factors through it; schematic density of the infinity overlap
then eliminates its kernel, even over the original nonreduced coefficient base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingProjectiveIsoProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "W" => smoothMarkingWeierstrassCurve E s e
local notation "f" => smoothMarkingToIntegralCubic E s e

/-- The finite original cubic map is a closed immersion over the entire original base. -/
theorem smoothMarkingToIntegralCubic_isClosedImmersion : IsClosedImmersion (f) := by
  let _ := smoothMarkingToIntegralCubic_finite E s e
  apply finite_isClosedImmersion_of_isIso_geometricFibers (f)
  intro K _ _ a
  have h := smoothMarkingCubicGeometricMap_isIso E s e (a ≫ integralCurveStructure (W))
  dsimp only [smoothMarkingCubicFieldMap] at h
  let _ := h
  exact relativeComparison_pullback_isIso (E.curve.hom ≫ S.toSpecΓ)
    (integralCurveStructure (W)) (f) (smoothMarkingToIntegralCubic_over E s e) a

/-- The original global cubic factorization is an isomorphism on the full relative curve. -/
theorem smoothMarkingToIntegralCubic_isIso : IsIso (f) := by
  let _ := smoothMarkingToIntegralCubic_isClosedImmersion E s e
  let Q := smoothMarkingIntegralAffineIso E s e
  apply integralCurve_closedImmersion_isIso_of_affineFactor (W) (f)
    (Q.inv ≫ Scheme.Opens.ι (X := E.curve.left) (t).left.ker.support.compl)
  dsimp only [Q]
  rw [Category.assoc, ← smoothMarkingIntegralAffineIso_chart, Iso.inv_hom_id_assoc]

/-- The complete relative presentation retains the original global coordinate morphism. -/
def smoothMarkingIntegralCubicIso : E.curve.left ≅ integralCurve (W) := by
  let _ := smoothMarkingToIntegralCubic_isIso E s e
  exact asIso (f)

/-- The full presentation preserves the original varying base map. -/
@[reassoc] theorem smoothMarkingIntegralCubicIso_over :
    (smoothMarkingIntegralCubicIso E s e).hom ≫ integralCurveStructure (W) =
      E.curve.hom ≫ S.toSpecΓ := smoothMarkingToIntegralCubic_over E s e

/-- The full presentation preserves the original specified marking. -/
@[reassoc] theorem smoothMarkingIntegralCubicIso_marking :
    (t).left ≫ (smoothMarkingIntegralCubicIso E s e).hom =
      S.toSpecΓ ≫ integralCurveZero (W) := smoothMarkingToIntegralCubic_marking E s e

/-- In particular the actual local rings at the original marking are isomorphic. -/
theorem smoothMarkingToIntegralCubic_marking_stalkMap_isIso (a : S) :
    IsIso ((f).stalkMap ((t).left a)) := by
  let _ := smoothMarkingToIntegralCubic_isIso E s e
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
