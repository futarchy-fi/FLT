/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChange

/-!
# Actual ample boundary parameters along arbitrary base refinements

The cartesian parameter comparison constructs maps for every triangle of base
schemes. Their identity and composition laws are equalities of actual scheme
maps, retaining both original parameter labels and the supplied base triangle.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleRefinementPullbackGroup_separated {W : Scheme} (f : W ⟶ S) :
    IsSeparated (E.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom f))

local instance ampleRefinementPullbackGroup_smooth {W : Scheme} (f : W ⟶ S) :
    SmoothOfRelativeDimension 1 (E.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom f
    inferInstance

/-- The actual parameter map induced by a supplied commuting triangle of bases. -/
def ampleBaseRefinement (g : T ⟶ S) (h : U ⟶ S) (f : U ⟶ T) (w : f ≫ g = h) :
    ampleParameter (E.baseChange h) n ⟶ ampleParameter (E.baseChange g) n :=
  (ampleBaseChangeToOriginal_isPullback g E n).lift (ampleBaseChangeToOriginal h E n)
    (ampleParameterBase (E.baseChange h) n ≫ f) (by
      rw [Category.assoc, w]
      exact (ampleBaseChangeToOriginal_isPullback h E n).w)

/-- Refinement retains the actual original ample parameter. -/
@[reassoc] theorem ampleBaseRefinement_original
    (g : T ⟶ S) (h : U ⟶ S) (f : U ⟶ T) (w : f ≫ g = h) :
    ampleBaseRefinement E n g h f w ≫ ampleBaseChangeToOriginal g E n =
      ampleBaseChangeToOriginal h E n :=
  (ampleBaseChangeToOriginal_isPullback g E n).lift_fst _ _ _

/-- Refinement retains exactly the supplied map of base schemes. -/
@[reassoc] theorem ampleBaseRefinement_base
    (g : T ⟶ S) (h : U ⟶ S) (f : U ⟶ T) (w : f ≫ g = h) :
    ampleBaseRefinement E n g h f w ≫ ampleParameterBase (E.baseChange g) n =
      ampleParameterBase (E.baseChange h) n ≫ f :=
  (ampleBaseChangeToOriginal_isPullback g E n).lift_snd _ _ _

/-- Identity base refinement acts identically on the actual ample boundary scheme. -/
@[simp] theorem ampleBaseRefinement_id (g : T ⟶ S) :
    ampleBaseRefinement E n g g (𝟙 T) (Category.id_comp g) = 𝟙 _ := by
  apply (ampleBaseChangeToOriginal_isPullback g E n).hom_ext
  · rw [ampleBaseRefinement_original, Category.id_comp]
  · rw [ampleBaseRefinement_base, Category.comp_id, Category.id_comp]

/-- Composing arbitrary supplied base refinements obeys the actual scheme cocycle law. -/
theorem ampleBaseRefinement_comp (g : T ⟶ S) (h : U ⟶ S) (k : V ⟶ S)
    (f : U ⟶ T) (j : V ⟶ U) (w : f ≫ g = h) (v : j ≫ h = k) :
    ampleBaseRefinement E n h k j v ≫ ampleBaseRefinement E n g h f w =
      ampleBaseRefinement E n g k (j ≫ f) (by rw [Category.assoc, w, v]) := by
  apply (ampleBaseChangeToOriginal_isPullback g E n).hom_ext
  · rw [Category.assoc, ampleBaseRefinement_original, ampleBaseRefinement_original,
      ampleBaseRefinement_original]
  · rw [Category.assoc, ampleBaseRefinement_base, ampleBaseRefinement_base_assoc,
      ampleBaseRefinement_base]

end FLT.Mazur.CyclicBoundaryParameter
