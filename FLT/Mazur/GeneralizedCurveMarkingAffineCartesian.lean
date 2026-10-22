/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicPreimages
public import FLT.Mazur.GeneralizedCurveMarkingAffineRestriction
public import FLT.Mazur.GeneralizedCurveIntegralMarkingAffineIso

/-!
# The original affine comparison is the actual cubic-chart pullback

Compose the retained affine isomorphism with the monic-chart comparison.
The exact preimage calculation proves that this square is Cartesian for the
global cubic map over the original varying base.

This specialization assumes integral geometric fibers, allowing singular cubics
but excluding higher polygons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingAffineCartesianProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (t)))) : E.curve.left.Opens)

/-- The original marked-point complement is isomorphic to the integral Z chart. -/
def smoothMarkingIntegralAffineIso :
    (Scheme.Opens.toScheme (X := E.curve.left) (U)) ≅ Spec (.of (Coordinate (W) 2)) :=
  smoothMarkingAffineIso E s e ≪≫
    Scheme.Spec.mapIso (affineChartMonicEquiv (W)).toRingEquiv.toCommRingCatIso.op

/-- The actual affine isomorphism restricts the global cubic factorization. -/
@[reassoc] theorem smoothMarkingIntegralAffineIso_chart :
    (smoothMarkingIntegralAffineIso E s e).hom ≫ integralCurveChart (W) 2 =
      (Scheme.Opens.ι (X := E.curve.left) (U)) ≫ smoothMarkingToIntegralCubic E s e :=
  (smoothMarkingToIntegralCubic_affine E s e).symm

/-- The retained affine comparison identifies the genuine preimage of the integral Z chart. -/
theorem smoothMarkingIntegralAffine_isPullback :
    IsPullback (smoothMarkingIntegralAffineIso E s e).hom (Scheme.Opens.ι (X := E.curve.left) (U))
      (integralCurveChart (W) 2) (smoothMarkingToIntegralCubic E s e) := by
  apply IsOpenImmersion.isPullback
  · exact (smoothMarkingIntegralAffineIso_chart E s e).symm
  · rw [smoothMarkingToIntegralCubic_preimage_z, Scheme.Opens.opensRange_ι]

/-- On the original marking complement the global cubic map is an open immersion. -/
theorem smoothMarkingToIntegralCubic_affine_isOpenImmersion :
    IsOpenImmersion ((Scheme.Opens.ι (X := E.curve.left) (U)) ≫
      smoothMarkingToIntegralCubic E s e) := by
  rw [← smoothMarkingIntegralAffineIso_chart]
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
