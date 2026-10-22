/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingLineBaseChange
public import FLT.Mazur.NodalGeometricFiberGenus
public import FLT.Mazur.PointedCurveLargeDegree
public import FLT.Mazur.ProperOnlyRelativeAmpleFibers
public import FLT.Mazur.RelativeAmpleFpqcDescent
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Ampleness of original markings with geometrically integral fibers

The original smooth marking has degree one on each integral geometric fiber,
including singular fibers. Fpqc descent and the proper fiber criterion give
relative ampleness over an arbitrary base without whole-curve smoothness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle Scheme.Modules.pullback

section Geometric
variable {K : Type} [Field K] [IsAlgClosed K]
  (E : GeneralizedEllipticCurve (Spec (.of K))) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group)

/-- A marking of an integral geometric generalized curve is ample, even at a nodal fiber. -/
theorem smoothMarkingLine_geometric_ample :
    AmpleLineBundle
      (divisorLineBundle (s ≫ E.inclusion).left.ker (E.smoothMarking_relativeCartier s).1) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : IsIntegral E.curve.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton E.curve.hom
  let hI := (E.smoothMarking_relativeCartier s).1
  have hf := E.family.genus.fiber K (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  apply ampleLineBundle_of_curveSheafDegree_pos E.curve.hom
    hf.toNodalFiberCore.topologicalKrullDim_eq_one.le hI.divisorLineBundle_locallyFreeRankOne
  rw [E.smoothMarkingLine_field_degree s]
  decide
end Geometric

section Field
variable {K : Type} [Field K]
  (E : GeneralizedEllipticCurve (Spec (.of K))) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group)

/-- Ampleness of the original marked line descends from the algebraic closure. -/
theorem smoothMarkingLine_field_ample :
    AmpleLineBundle
      (divisorLineBundle (s ≫ E.inclusion).left.ker (E.smoothMarking_relativeCartier s).1) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let g := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let _ : Flat g := inferInstance
  let _ : Surjective g := ⟨Function.surjective_to_subsingleton g⟩
  let _ : QuasiCompact g := inferInstance
  let _ : GeometricallyIntegral (E.baseChange g).curve.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd E.curve.hom g))
  let hL := (E.smoothMarking_relativeCartier s).1.divisorLineBundle_locallyFreeRankOne
  have ha := ((E.baseChange g).smoothMarkingLine_geometric_ample (pullSection g s)).of_iso
    (E.smoothMarkingLineBaseChangeIso g s)
  have hb := ((ha.relative_of_affine (pullback.snd E.curve.hom g)).relativeAmple).of_fpqc
    hL (IsPullback.of_hasPullback E.curve.hom g)
  exact (hb.relativelyAmpleLineBundle hL).ample_of_affine
end Field

variable {S : Scheme} (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- The actual marking line is ample on every field fiber with integral geometric fibers. -/
theorem smoothMarkingLine_fieldFiber_ample {K : Type} [Field K] (g : Spec (.of K) ⟶ S) :
    AmpleLineBundle ((Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj
      (divisorLineBundle (s ≫ E.inclusion).left.ker (E.smoothMarking_relativeCartier s).1)) := by
  let _ : GeometricallyIntegral (E.baseChange g).curve.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd E.curve.hom g))
  exact ((E.baseChange g).smoothMarkingLine_field_ample (pullSection g s)).of_iso
    (E.smoothMarkingLineBaseChangeIso g s)

/-- Integral geometric fibers give relative ampleness of the original marking on any base. -/
theorem smoothMarkingLine_relativeAmple :
    RelativeAmple E.curve.hom
      (divisorLineBundle (s ≫ E.inclusion).left.ker (E.smoothMarking_relativeCartier s).1) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  apply relativeAmple_of_ample_fibers_proper E.curve.hom _
    (E.smoothMarking_relativeCartier s).1.divisorLineBundle_locallyFreeRankOne
  intro z
  exact E.smoothMarkingLine_fieldFiber_ample s (S.fromSpecResidueField z)

/-- Over an affine base the original marking line is ample on the whole integral-fiber family. -/
theorem smoothMarkingLine_ample [IsAffine S] :
    AmpleLineBundle
      (divisorLineBundle (s ≫ E.inclusion).left.ker (E.smoothMarking_relativeCartier s).1) :=
  ((E.smoothMarkingLine_relativeAmple s).relativelyAmpleLineBundle
    (E.smoothMarking_relativeCartier s).1.divisorLineBundle_locallyFreeRankOne).ample_of_affine

end FLT.Mazur.GeneralizedEllipticCurve
