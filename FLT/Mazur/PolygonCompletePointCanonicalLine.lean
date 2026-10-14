/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointPushforwardLine
public import FLT.Mazur.NeutralTwistDirectImage
public import FLT.Mazur.RelativeRankOneDivisorUniqueness

/-!
# The canonical degree-one direct image over the complete base

Affine reconstruction of the proved rank-one section module makes the actual
pushforward a line. The original relative Cartier section then trivializes it.
No smoothness or group structure of the total polygon is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionNeutralTwistIso
  twistedSectionPushforwardEquiv

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original canonical divisor section trivializes its actual direct image. -/
theorem completePointCanonicalSectionMap_isIso (i : Fin n) :
    IsIso (sectionDirectImageMap (exactVeroneseProjToBase K n h)
      (completePointLine K n h i)
      (divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := completePointFamily_surjective K n h i
  let a := sectionDivisorRelativeSection (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1
  have hn := completePointLine_pushforward_rankOne K n h i
  have hi := (relativeSection_directImage_locallySplit (exactVeroneseProjToBase K n h) _
    (completePointLine_locallyFreeRankOne K n h i) hn.locallyFiniteFree a).isIso _
      structureModule_locallyFreeRankOne.dual hn
  change IsIso (twistedSectionPushforwardEquiv (exactVeroneseProjToBase K n h) _
    structureModule_locallyFreeRankOne
    ((sectionNeutralTwistIso (exactVeroneseProjToBase K n h) _).inv.app ⊤
      (divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤))) at hi
  rw [neutralTwist_directImage] at hi
  let _ : IsIso (moduleSheafDualUnitIso.hom ≫
      sectionDirectImageMap (exactVeroneseProjToBase K n h) (completePointLine K n h i)
        (divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤)) := hi
  exact IsIso.of_isIso_comp_left moduleSheafDualUnitIso.hom _

/-- The isomorphism is the ordinary adjoint of the original canonical divisor section. -/
def completePointCanonicalSectionIso (i : Fin n) :
    structureModule (Spec (.of (PowerSeries K))) ≅
      (pushforward (exactVeroneseProjToBase K n h)).obj (completePointLine K n h i) := by
  let _ := completePointCanonicalSectionMap_isIso K n h i
  exact asIso (sectionDirectImageMap (exactVeroneseProjToBase K n h)
      (completePointLine K n h i)
    (divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤))

end FLT.Mazur.PolygonInfinitesimalStages
