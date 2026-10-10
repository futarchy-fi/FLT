/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFramedLineHomExt
public import FLT.Mazur.AffineSectionLineReversePoint
public import FLT.Mazur.AffineSplitLineCoordinatePullback

/-!
# Canonical geometric pullback of the actual affine section line

The original normalized coordinate frames construct a geometric line
comparison. Recovered vectors prove that it preserves the original
inclusion through the canonical pullback comparison for free sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open NormalizedSectionLine AffineSplitLineCoordinates
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {ι : Type u} [Finite ι]

/-- Geometric pullback of the actual line, compared using its original coordinate frame. -/
def canonicalSectionLinePullback (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    (pullback f).obj (sectionLineSheaf Y i L) ≅
      sectionLineSheaf X i (baseChange f.appTop.hom i L) :=
  SplitSheafLinePullback.frame f (sectionLineTrivialization Y i L) ≪≫
    (sectionLineTrivialization X i (baseChange f.appTop.hom i L)).symm

/-- Pullback of the original inclusion has the extended normalized vector. -/
lemma sectionLineInclusion_pullback_vector (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    vector (SplitSheafLinePullback.frame f (sectionLineTrivialization Y i L))
        (SplitSheafLinePullback.inclusion f (sectionLineInclusion Y i L)) =
      vector (sectionLineTrivialization X i (baseChange f.appTop.hom i L))
        (sectionLineInclusion X i (baseChange f.appTop.hom i L)) := by
  rw [vector_pullback, vector_sectionLineInclusion, vector_sectionLineInclusion,
    generator_baseChange]

/-- The comparison identifies the actual geometric inclusion with canonical free pullback. -/
lemma canonicalSectionLinePullback_inclusion (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    (canonicalSectionLinePullback f i L).hom ≫
        sectionLineInclusion X i (baseChange f.appTop.hom i L) =
      (pullback f).map (sectionLineInclusion Y i L) ≫
        (ModuleGlobalEvaluationPullback.freeIso f ι).hom :=
  frameCompare_inclusion _ _ _ _ (sectionLineInclusion_pullback_vector f i L)

instance (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    Mono (SplitSheafLinePullback.inclusion f (sectionLineInclusion Y i L)) := by
  dsimp only [SplitSheafLinePullback.inclusion]
  infer_instance

/-- The actual pulled line and the extended section line are the same ambient subobject. -/
lemma canonicalSectionLinePullback_subobject (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    Subobject.mk (SplitSheafLinePullback.inclusion f (sectionLineInclusion Y i L)) =
      Subobject.mk (sectionLineInclusion X i (baseChange f.appTop.hom i L)) :=
  Subobject.mk_eq_mk_of_comm _ _ (canonicalSectionLinePullback f i L)
    (canonicalSectionLinePullback_inclusion f i L)

/-- The ambient inclusion uniquely determines the geometric line comparison. -/
lemma canonicalSectionLinePullback_unique (i : ι) (L : Chart Γ(Y, ⊤) ι i)
    (a : (pullback f).obj (sectionLineSheaf Y i L) ⟶
      sectionLineSheaf X i (baseChange f.appTop.hom i L))
    (ha : a ≫ sectionLineInclusion X i (baseChange f.appTop.hom i L) =
      (pullback f).map (sectionLineInclusion Y i L) ≫
        (ModuleGlobalEvaluationPullback.freeIso f ι).hom) :
    a = (canonicalSectionLinePullback f i L).hom := by
  apply (cancel_mono (sectionLineInclusion X i (baseChange f.appTop.hom i L))).mp
  rw [ha, canonicalSectionLinePullback_inclusion]

end FLT.Mazur.AffineFreeSheafCoordinates
