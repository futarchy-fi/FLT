/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneUnrestrictedPointPowers
public import FLT.Mazur.SmoothAffineGeometricVanishing

/-!
# Actual higher pole cohomology over unrestricted original bases

The original positive pole powers are acyclic for direct image on every base.
Over an affine base this kills their actual positive global cohomology.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (m : ℕ) (hm : 0 < m)

include hg hm in
/-- Positive pole powers have zero higher direct images over every original base. -/
theorem relative_pointPower_higherImage_unrestricted :
    ModulePushforwardAcyclic G.hom (tensorPower (divisorLineBundle s.left.ker hI) m) := by
  let _ := SmoothOfRelativeDimension.smooth 1 G.hom
  exact smooth_geometricAcyclic_higherImage G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_geometric_acyclic_unrestricted G hg s hI m hm)

include hg hm in
/-- Positive pole cohomology vanishes over arbitrary affine original bases. -/
theorem relative_pointPower_acyclic_unrestricted [IsAffine S] (n : ℕ) :
    Subsingleton (ModuleH (tensorPower (divisorLineBundle s.left.ker hI) m) (n + 1)) := by
  let _ := SmoothOfRelativeDimension.smooth 1 G.hom
  exact smoothAffine_geometricAcyclic_positive_vanishing G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)
    (relative_pointPower_geometric_acyclic_unrestricted G hg s hI m hm) n

end FLT.Mazur.FCurve
