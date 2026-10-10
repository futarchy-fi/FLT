/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineCanonicalPullback
public import FLT.Mazur.LocallySplitLineOpenRestriction

/-!
# Ordinary restriction of actual affine section lines

The canonical comparison identifies the original restricted line inclusion
with the coefficient-extended line, using the free restriction coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open NormalizedSectionLine ModuleGlobalEvaluationPullback SplitLineAffinePresentation
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
variable (f : X ⟶ Y) [IsOpenImmersion f] {ι : Type u} [Finite ι]

/-- The actual restriction of the original line is the extended section-line sheaf. -/
def canonicalSectionLineRestriction (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    (sectionLineSheaf Y i L).restrict f ≅
      sectionLineSheaf X i (baseChange f.appTop.hom i L) :=
  (restrictFunctorIsoPullback f).app _ ≪≫ canonicalSectionLinePullback f i L

/-- Restriction preserves inclusion through the same free comparison as ambient charts. -/
lemma canonicalSectionLineRestriction_inclusion (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    (canonicalSectionLineRestriction f i L).hom ≫
        sectionLineInclusion X i (baseChange f.appTop.hom i L) =
      (restrictFunctor f).map (sectionLineInclusion Y i L) ≫ (freeRestrictIso f ι).hom := by
  change ((restrictFunctorIsoPullback f).hom.app _ ≫
    (canonicalSectionLinePullback f i L).hom) ≫ _ = _
  rw [Category.assoc, canonicalSectionLinePullback_inclusion]
  exact restrictedInclusion_comparison f (sectionLineInclusion Y i L)

instance (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    Mono (restrictedInclusion f (sectionLineInclusion Y i L)) := by
  dsimp only [restrictedInclusion]
  infer_instance

/-- Equality holds for the actual subobjects, not just their coordinate modules. -/
lemma canonicalSectionLineRestriction_subobject (i : ι) (L : Chart Γ(Y, ⊤) ι i) :
    Subobject.mk (restrictedInclusion f (sectionLineInclusion Y i L)) =
      Subobject.mk (sectionLineInclusion X i (baseChange f.appTop.hom i L)) :=
  Subobject.mk_eq_mk_of_comm _ _ (canonicalSectionLineRestriction f i L)
    (canonicalSectionLineRestriction_inclusion f i L)

end FLT.Mazur.AffineFreeSheafCoordinates
