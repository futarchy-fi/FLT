/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineSectionCoordinates
public import FLT.Mazur.SplitSheafLinePullback

/-!
# Geometric pullback of recovered split-line vectors

The actual free-sheaf section comparison identifies pullback with entrywise
coefficient change. Hence coordinates recovered from the original sheaf
inclusion commute with arbitrary affine geometric pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open AffineModuleGlobalSections AffineFreeSheafCoordinates FreeSheafSectionCoordinates FCurve
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {ι : Type u} [Finite ι]

/-- Vector realization identifies the geometric and entrywise coefficient pullbacks. -/
lemma vectorSectionIso_pullback (v : ι → Γ(Y, ⊤)) :
    (ModuleGlobalEvaluationPullback.freeIso f ι).hom.app ⊤
      (pullGlobal f _ ((vectorSectionIso Y ι).hom v)) =
        (vectorSectionIso X ι).hom (fun i ↦ f.appTop (v i)) := by
  rw [vectorSectionIso_apply, vectorSectionIso_apply, realize_pullback]
  congr 1
  ext i
  rfl

/-- The recovered vector of the actual pulled sheaf inclusion is its coefficient image. -/
lemma vector_pullback {L : Y.Modules} (e : L ≅ structureModule Y)
    (s : L ⟶ SheafOfModules.free ι) :
    vector (SplitSheafLinePullback.frame f e) (SplitSheafLinePullback.inclusion f s) =
      fun i ↦ f.appTop (vector e s i) := by
  apply (vectorSectionIso X ι).toLinearEquiv.injective
  change (vectorSectionIso X ι).hom _ = (vectorSectionIso X ι).hom _
  rw [vectorSectionIso_vector, ← vectorSectionIso_pullback, vectorSectionIso_vector]
  exact SplitSheafLinePullback.inclusion_frame_section f e s

/-- Every affine open restriction uses the original restriction map on coefficients. -/
lemma vector_open {L : Y.Modules} (e : L ≅ structureModule Y)
    (s : L ⟶ SheafOfModules.free ι) (U : Y.Opens) [IsAffine U.toScheme] :
    vector (SplitSheafLinePullback.frame U.ι e) (SplitSheafLinePullback.inclusion U.ι s) =
      fun i ↦ U.ι.appTop (vector e s i) := vector_pullback U.ι e s

/-- The original retraction certifies the pulled coordinate vector's principal cover. -/
lemma pulled_vector_retraction {L : Y.Modules} (e : L ≅ structureModule Y)
    (s : L ⟶ SheafOfModules.free ι) (r : SheafOfModules.free ι ⟶ L)
    (hs : s ≫ r = 𝟙 L) :
    retraction (SplitSheafLinePullback.frame f e) (SplitSheafLinePullback.retraction f r)
      (fun i ↦ f.appTop (vector e s i)) = 1 := by
  rw [← vector_pullback]
  exact vector_retraction _ _ _ (SplitSheafLinePullback.inclusion_retraction f s r hs)

end FLT.Mazur.AffineSplitLineCoordinates
