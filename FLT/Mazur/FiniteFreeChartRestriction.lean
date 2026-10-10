/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartTransitions
public import FLT.Mazur.OpenModuleRestrictionCoherence

/-!
# Restriction coherence of finite free chart transitions

Refining a free chart in two stages agrees with direct refinement. Consequently
coordinate transitions restrict by the canonical free sheaf comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FiniteFreeChartTransitions
open OpenModuleRestrictionCoherence ModuleGlobalEvaluationPullback
variable {X : Scheme.{u}} (M : X.Modules)

/-- Refining a chart twice agrees with refining directly to the smallest open. -/
lemma refineChart_comp {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) {ι : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    refineChart M (k.trans h) e = nested M k ≪≫
      (restrictFunctor (X.homOfLE k)).mapIso (refineChart M h e) ≪≫
        freeRestrictIso (X.homOfLE k) ι := by
  have hn := congrArg Iso.hom (nested_comp M h k)
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hn
  apply Iso.ext
  change (nested M (k.trans h)).hom ≫
    (restrictFunctor (X.homOfLE (k.trans h))).map e.hom ≫
    (freeRestrictIso (X.homOfLE (k.trans h)) ι).hom = _
  change _ = (nested M k).hom ≫
    (restrictFunctor (X.homOfLE k)).map
      ((nested M h).hom ≫ (restrictFunctor (X.homOfLE h)).map e.hom ≫
        (freeRestrictIso (X.homOfLE h) ι).hom) ≫
      (freeRestrictIso (X.homOfLE k) ι).hom
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (nested M k).hom, ← hn]
  have he := (inclusionComp h k).hom.naturality e.hom
  dsimp only [Functor.comp_map] at he
  rw [Category.assoc, ← reassoc_of% he]
  rw [free_inclusionComp]

/-- Transition maps commute with further restriction of their common refinement. -/
lemma transition_restrict {U V W T : X.Opens} (hU : W ≤ U) (hV : W ≤ V) (k : T ≤ W)
    {ι κ : Type u} (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    transition M (k.trans hU) (k.trans hV) e d =
      (freeRestrictIso (X.homOfLE k) ι).symm ≪≫
        (restrictFunctor (X.homOfLE k)).mapIso (transition M hU hV e d) ≪≫
          freeRestrictIso (X.homOfLE k) κ := by
  apply Iso.ext
  simp only [transition]
  rw [refineChart_comp M hU k, refineChart_comp M hV k]
  simp

end FLT.Mazur.FiniteFreeChartTransitions
