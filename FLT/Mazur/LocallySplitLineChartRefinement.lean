/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineOpenRestriction
public import FLT.Mazur.LocallySplitLineAmbientChart

/-!
# Reverse points under actual ambient chart refinement

Restriction through nested base opens preserves the original sheaf inclusion.
Thus the reverse point in the refined finite free chart is the restriction
of the point in the original chart, with its genuine coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.OpenModuleRestrictionCoherence
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)
variable {U V : X.Opens} (h : U ≤ V)

/-- The nested restriction comparison is natural in the original sheaf inclusion. -/
lemma nested_naturality :
    (nested L h).hom ≫ (restrictFunctor (X.homOfLE h)).map
        ((restrictFunctor V.ι).map s) =
      (restrictFunctor U.ι).map s ≫ (nested M h).hom :=
  ((restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
    restrictFunctorComp (X.homOfLE h) V.ι).hom.naturality s).symm

end FLT.Mazur.OpenModuleRestrictionCoherence

namespace FLT.Mazur.LocallySplitLineAmbientChart
open FCurve SplitLineAffineNeighborhood SplitLineAffinePresentation
open OpenModuleRestrictionCoherence FiniteFreeChartTransitions ModuleGlobalEvaluationPullback
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)
variable {U V : X.Opens} (h : U ≤ V) {ι : Type u} [Finite ι]
variable (e : M.restrict V.ι ≅ SheafOfModules.free ι)

omit [Finite ι] in
/-- The refined chart uses the same original inclusion as ordinary nested restriction. -/
lemma inclusion_refinement :
    (nested L h).hom ≫ restrictedInclusion (X.homOfLE h) (inclusion s V e) =
      inclusion s U (refineChart M h e) := by
  change (nested L h).hom ≫
    ((restrictFunctor (X.homOfLE h)).map
      ((restrictFunctor V.ι).map s ≫ e.hom) ≫ (freeRestrictIso _ ι).hom) =
        (restrictFunctor U.ι).map s ≫
          ((nested M h).hom ≫ (restrictFunctor (X.homOfLE h)).map e.hom ≫
            (freeRestrictIso _ ι).hom)
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  rw [nested_naturality]

variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)

/-- The actual reverse point commutes with ambient chart refinement and coefficient change. -/
lemma point_refinement :
    X.homOfLE h ≫ point s hL hs V e =
      point s hL hs U (refineChart M h e) ≫
        ProjectiveSpace.coefficientMap (X.homOfLE h).appTop.hom ι := by
  unfold point
  rw [morphism_restriction]
  apply congrArg (· ≫ ProjectiveSpace.coefficientMap (X.homOfLE h).appTop.hom ι)
  exact (morphism_sourceIso (nested L h)
    (inclusion s U (refineChart M h e))
    (restrictedInclusion (X.homOfLE h) (inclusion s V e))
    (inclusion_refinement s h e) _ _ _ _).symm

end FLT.Mazur.LocallySplitLineAmbientChart
