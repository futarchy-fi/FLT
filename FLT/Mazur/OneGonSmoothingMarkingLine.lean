/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingFamily
public import FLT.Mazur.WeierstrassOriginCartier
public import FLT.Mazur.PrincipalSectionExtension
public import FLT.Mazur.DivisorLinePullback
public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.RelativeCartierBaseChange
public import FLT.Mazur.SectionCartesianKernel

/-!
# The actual infinity marking line on the one-gon smoothing

Dualize the intrinsic infinity-section ideal. Its proved relative Cartier
property gives a coherent rank-one line and preserves it under coefficient change.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open FCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (t : R)

/-- The actual infinity section is a relative effective Cartier divisor. -/
theorem marking_relativeCartier : RelativeEffectiveCartier (family t).hom (marking t).ker :=
  originIdealSheaf_relativeCartier (equation t)

/-- The positive line of the original infinity marking, with its actual ideal. -/
def markingLine : (family t).left.Modules :=
  divisorLineBundle (marking t).ker (marking_relativeCartier t).1

/-- The original infinity marking line is locally free of rank one. -/
theorem markingLine_rankOne : LocallyFreeRankOne (markingLine t) :=
  (marking_relativeCartier t).1.divisorLineBundle_locallyFreeRankOne

/-- The original marking line is a finitely presented sheaf. -/
theorem markingLine_isFinitePresentation {A : Type} [CommRing A] (a : A) :
    (markingLine a).IsFinitePresentation :=
  (markingLine_rankOne a).isFinitePresentation

variable {S : Scheme.{u}} (s : S ⟶ Spec (.of R))

/-- The retained infinity marking on an arbitrary scheme base change. -/
def fiberMarking : S ⟶ pullback (family t).hom s :=
  pullback.lift (s ≫ marking t) (𝟙 S)
    (by rw [Category.assoc, marking_toBase, Category.comp_id, Category.id_comp])

/-- The retained section has the original infinity point as its curve projection. -/
@[reassoc] theorem fiberMarking_fst :
    fiberMarking t s ≫ pullback.fst _ _ = s ≫ marking t := pullback.lift_fst _ _ _

/-- The retained marking is a section of the actual base-changed family. -/
@[reassoc] theorem fiberMarking_snd :
    fiberMarking t s ≫ pullback.snd _ _ = 𝟙 S := pullback.lift_snd _ _ _

/-- The actual infinity ideal pulls back to the actual retained section ideal. -/
theorem marking_ker_comap :
    (marking t).ker.comap (pullback.fst (family t).hom s) = (fiberMarking t s).ker := by
  let _ := family_proper t
  exact section_ker_comap_of_cartesian (IsPullback.of_hasPullback _ _)
    (fiberMarking t s) (marking t) (fiberMarking_snd t s) (marking_toBase t)
    (fiberMarking_fst t s)

/-- The retained marking remains relative effective Cartier after arbitrary base change. -/
theorem fiberMarking_relativeCartier :
    RelativeEffectiveCartier (pullback.snd (family t).hom s) (fiberMarking t s).ker := by
  rw [← marking_ker_comap]
  exact relativeCartierBaseChange _ _ _ (marking_relativeCartier t)

/-- The positive line of the retained infinity section. -/
def fiberMarkingLine : (pullback (family t).hom s).Modules :=
  divisorLineBundle (fiberMarking t s).ker (fiberMarking_relativeCartier t s).1

/-- The canonical comparison on the actual marking ideals is invertible. -/
instance markingIdeal_baseChange_isIso :
    IsIso (idealModulePullbackHom (marking t).ker (pullback.fst (family t).hom s)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (marking_relativeCartier t).1
  rw [marking_ker_comap]
  exact (fiberMarking_relativeCartier t s).1

/-- The retained infinity line is the canonical pullback of the original marking line. -/
def markingLineBaseChangeIso :
    (Scheme.Modules.pullback (pullback.fst (family t).hom s)).obj (markingLine t) ≅
      fiberMarkingLine t s :=
  divisorLinePullbackIsoOfEq _ (marking_relativeCartier t).1
    (fiberMarking_relativeCartier t s).1 (marking_ker_comap t s)

end FLT.Mazur.OneGonSmoothing
