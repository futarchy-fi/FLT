/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneUnrestrictedPointLine
public import FLT.Mazur.SectionDivisorNeutralTwist
public import FLT.Mazur.RelativeRankOneDivisorUniqueness

/-!
# The canonical degree-one section over unrestricted original bases

The actual canonical divisor section identifies the original degree-one
direct image with the dual structure line, also over nonnoetherian bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback CartierAbel ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {S : Scheme}
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg in
/-- The direct-image map of the actual canonical section is invertible. -/
theorem relative_canonicalSection_directImage_isIso_unrestricted :
    IsIso ((sectionDivisorNeutralSection G.hom s.left hI).toDirectImage G.hom _).map := by
  let a := sectionDivisorRelativeSection G.hom s.left s.w hI
  have hn := relative_pointLine_pushforward_rankOne_unrestricted G hg s hI
  exact (relativeSection_directImage_locallySplit G.hom _
    hI.divisorLineBundle_locallyFreeRankOne hn.locallyFiniteFree a).isIso _
      structureModule_locallyFreeRankOne.dual hn

/-- The isomorphism retains the direct image of the original canonical section. -/
def relativeCanonicalSectionDirectImageIsoUnrestricted :
    moduleSheafDual (structureModule S) ≅
      (pushforward G.hom).obj (divisorLineBundle s.left.ker hI) := by
  let _ := relative_canonicalSection_directImage_isIso_unrestricted G hg s hI
  exact asIso ((sectionDivisorNeutralSection G.hom s.left hI).toDirectImage G.hom _).map

/-- The isomorphism uses exactly the original canonical direct-image map. -/
theorem relativeCanonicalSectionDirectImageIsoUnrestricted_hom :
    (relativeCanonicalSectionDirectImageIsoUnrestricted G hg s hI).hom =
      ((sectionDivisorNeutralSection G.hom s.left hI).toDirectImage G.hom _).map := rfl

end FLT.Mazur.FCurve
