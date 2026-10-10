/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparatedOverlapPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Product maps of actual open intersections

The intersection of two opens maps to their product over the specified base.
These maps test separatedness and retain local finite type from the structure map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens)

/-- The actual open intersection mapped to the product of its charts over the base. -/
def openIntersectionProduct : (U ⊓ V).toScheme ⟶ pullback (U.ι ≫ f) (V.ι ≫ f) :=
  pullback.lift (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) (by simp)

@[reassoc (attr := simp)] theorem openIntersectionProduct_fst :
    openIntersectionProduct f U V ≫ pullback.fst _ _ = X.homOfLE inf_le_left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem openIntersectionProduct_snd :
    openIntersectionProduct f U V ≫ pullback.snd _ _ = X.homOfLE inf_le_right :=
  pullback.lift_snd _ _ _

/-- Local finite type of the structure map suffices for the intersection product map. -/
instance openIntersectionProduct_locallyOfFiniteType [LocallyOfFiniteType f] :
    LocallyOfFiniteType (openIntersectionProduct f U V) := by
  have he : openIntersectionProduct f U V ≫ (pullback.fst _ _ ≫ U.ι ≫ f) =
      (U ⊓ V).ι ≫ f := by simp
  let _ : LocallyOfFiniteType
      (openIntersectionProduct f U V ≫ (pullback.fst _ _ ≫ U.ι ≫ f)) :=
    he.symm ▸ inferInstance
  exact locallyOfFiniteType_of_comp _ (pullback.fst _ _ ≫ U.ι ≫ f)

/-- Closed intersection product maps on an open cover imply separatedness. -/
theorem isSeparated_of_openIntersectionProduct {K : Type v} (W : K → X.Opens)
    (hW : TopologicalSpace.IsOpenCover W)
    (h : ∀ i j, IsClosedImmersion (openIntersectionProduct f (W i) (W j))) :
    IsSeparated f := by
  exact SeparatedOpenCover.of_overlap_pullbacks f (X.openCoverOfIsOpenCover W hW)
    (fun i j ↦ (W i ⊓ W j).toScheme) (fun _ _ ↦ X.homOfLE inf_le_left)
    (fun _ _ ↦ X.homOfLE inf_le_right) (fun i j ↦ isPullback_opens_inf (W i) (W j)) h

end FLT.Mazur.Approximation
