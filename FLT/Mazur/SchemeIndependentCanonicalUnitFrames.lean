/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackUnitCoherence
public import FLT.Mazur.SchemeIndependentCanonicalCocycle

/-!
# Canonical overlaps preserve the structure-module frames

The unit pullback comparison is compatible with normalization along a specified
composite path. Consequently its original member frames agree on unequal pairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentCanonicalOverlap
open FCurve SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z Y₁ Y₂ : Scheme.{u}}

/-- The unit comparison respects the specified normalization of a pullback path. -/
lemma comparison_unit (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k) :
    (comparison f g k w).hom.app (structureModule Z) ≫ (modulePullbackUnitIso k).hom =
      (pullback f).map (modulePullbackUnitIso g).hom ≫ (modulePullbackUnitIso f).hom := by
  subst k
  simpa only [comparison, Iso.trans_hom, NatTrans.comp_app, pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
    (modulePullbackUnitIso_comp_hom f g).symm

/-- Canonical unequal pair maps intertwine the original structure-module frames. -/
lemma pair_unit (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) :
    (pair f g (structureModule X)).hom ≫
        (pullback (Limits.pullback.snd f g)).map (modulePullbackUnitIso g).hom ≫
        (modulePullbackUnitIso (Limits.pullback.snd f g)).hom =
      (pullback (Limits.pullback.fst f g)).map (modulePullbackUnitIso f).hom ≫
        (modulePullbackUnitIso (Limits.pullback.fst f g)).hom := by
  rw [← comparison_unit (Limits.pullback.snd f g) g
    (Limits.pullback.fst f g ≫ f) Limits.pullback.condition.symm]
  dsimp only [pair, overlap, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [Category.assoc, Iso.inv_hom_id_app_assoc, comparison_unit]

end FLT.Mazur.SchemeIndependentCanonicalOverlap
