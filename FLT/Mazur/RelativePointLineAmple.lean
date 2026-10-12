/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCurveLargeDegree
public import FLT.Mazur.SectionPointPowerBaseChange
public import FLT.Mazur.GroupSectionBaseChange
public import FLT.Mazur.SmoothDimensionBound
public import FLT.Mazur.ProperOnlyRelativeAmpleFibers
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Ampleness of the original relative point line

The retained point has degree one on every field fiber. Properness promotes
fiberwise ampleness to relative ampleness of the original divisor line.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.FCurve
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {S : Scheme.{0}} (G : Over S) [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- The original point line is ample on every field fiber, with no genus hypothesis. -/
theorem relative_pointLine_field_ample {k : Type} [Field k] (g : Spec (.of k) ⟶ S) :
    AmpleLineBundle ((Scheme.Modules.pullback (pullback.fst G.hom g)).obj
      (divisorLineBundle s.left.ker hI)) := by
  let H := (Over.pullback g).obj G
  let _ : IsProper H.hom := inferInstanceAs (IsProper (pullback.snd G.hom g))
  let _ : SmoothOfRelativeDimension 1 H.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom g)
      (inferInstance : SmoothOfRelativeDimension 1 G.hom)
  let _ : IsIntegral H.left := GeometricallyIntegral.geometrically_isIntegral
    g _ _ (IsPullback.of_hasPullback G.hom g)
  let t := pullSection g s
  let hJ := sectionPoint_cartier_baseChange (IsPullback.of_hasPullback G.hom g)
    s.left t.left s.w t.w (section_fst g s) hI
  have ha : AmpleLineBundle (divisorLineBundle t.left.ker hJ) := by
    apply ampleLineBundle_of_curveSheafDegree_pos H.hom
      (topologicalKrullDim_le_one_of_smooth H.hom) hJ.divisorLineBundle_locallyFreeRankOne
    rw [pointedCurve_line_degree_one H.hom t.left t.w]
    decide
  exact ha.of_iso (sectionPointLineIso (IsPullback.of_hasPullback G.hom g)
    s.left t.left s.w t.w (section_fst g s) hI hJ)

/-- The actual section line is relatively ample on a proper smooth integral curve family. -/
theorem relative_pointLine_relativeAmple :
    RelativeAmple G.hom (divisorLineBundle s.left.ker hI) := by
  apply relativeAmple_of_ample_fibers_proper G.hom _ hI.divisorLineBundle_locallyFreeRankOne
  intro z
  exact relative_pointLine_field_ample G s hI (S.fromSpecResidueField z)

/-- Over an affine base the original point line is ample on the total space. -/
theorem relative_pointLine_ample [IsAffine S] :
    AmpleLineBundle (divisorLineBundle s.left.ker hI) :=
  ((relative_pointLine_relativeAmple G s hI).relativelyAmpleLineBundle
    hI.divisorLineBundle_locallyFreeRankOne).ample_of_affine

end FLT.Mazur.FCurve
