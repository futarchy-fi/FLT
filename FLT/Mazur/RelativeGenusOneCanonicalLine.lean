/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointFrames
public import FLT.Mazur.SectionDivisorNeutralTwist
public import FLT.Mazur.RelativeRankOneDivisorUniqueness

/-!
# The canonical degree-one direct-image line

The genus-one fiber calculation makes the original degree-one direct image a
line. The original canonical divisor section, with its neutral base twist,
then gives an isomorphism from the dual structure module to that direct image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback CartierAbel ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

include hg in
/-- The original degree-one pole direct image is a line on the entire affine base. -/
theorem relative_pointOne_pushforward_rankOne :
    LocallyFreeRankOne ((pushforward G.hom).obj
      (tensorPower (divisorLineBundle s.left.ker hI) 1)) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := relative_pointPower_frame G hg s hI 1 (by decide) x
  exact ⟨U, hx, ⟨e ≪≫ Limits.coproductUniqueIso
    (fun _ : Fin 1 ↦ structureModule U.toScheme)⟩⟩

include hg in
/-- Removing the degree-one tensor unitor gives the original divisor-line direct image. -/
theorem relative_pointLine_pushforward_rankOne :
    LocallyFreeRankOne ((pushforward G.hom).obj (divisorLineBundle s.left.ker hI)) :=
  (relative_pointOne_pushforward_rankOne G hg s hI).of_iso
    ((pushforward G.hom).mapIso (rightUnitor (divisorLineBundle s.left.ker hI)))

include hg in
/-- The direct-image map of the actual canonical section is invertible. -/
theorem relative_canonicalSection_directImage_isIso :
    IsIso ((sectionDivisorNeutralSection G.hom s.left hI).toDirectImage G.hom _).map := by
  let a := sectionDivisorRelativeSection G.hom s.left s.w hI
  have hn := relative_pointLine_pushforward_rankOne G hg s hI
  exact (relativeSection_directImage_locallySplit G.hom _
    hI.divisorLineBundle_locallyFreeRankOne hn.locallyFiniteFree a).isIso _
      structureModule_locallyFreeRankOne.dual hn

/-- The isomorphism retains the direct image of the original canonical section. -/
def relativeCanonicalSectionDirectImageIso :
    moduleSheafDual (structureModule S) ≅
      (pushforward G.hom).obj (divisorLineBundle s.left.ker hI) := by
  let _ := relative_canonicalSection_directImage_isIso G hg s hI
  exact asIso ((sectionDivisorNeutralSection G.hom s.left hI).toDirectImage G.hom _).map

/-- The isomorphism uses exactly the original canonical direct-image map. -/
theorem relativeCanonicalSectionDirectImageIso_hom :
    (relativeCanonicalSectionDirectImageIso G hg s hI).hom =
      ((sectionDivisorNeutralSection G.hom s.left hI).toDirectImage G.hom _).map := rfl

end FLT.Mazur.FCurve
