/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeSheafRestrictionCoherence

/-!
# Restriction paths through nested opens

The canonical comparisons between direct and iterated restrictions agree
on every section. This supplies the source coherence for free chart refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace FLT.Mazur.OpenModuleRestrictionCoherence
variable {X : Scheme.{u}}

/-- The direct restriction to a smaller open compared with restriction through a larger open. -/
def nested (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    M.restrict V.ι ≅ (M.restrict U.ι).restrict (X.homOfLE h) :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M

/-- The comparison along two inclusions of opens. -/
def inclusionComp {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) :
    restrictFunctor (X.homOfLE (k.trans h)) ≅
      restrictFunctor (X.homOfLE h) ⋙ restrictFunctor (X.homOfLE k) :=
  restrictFunctorCongr (X.homOfLE_homOfLE k h).symm ≪≫
    restrictFunctorComp (X.homOfLE k) (X.homOfLE h)

/-- Normalizing an equality of restriction maps twice does not alter a section. -/
lemma congr_refl {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) :
    (restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  simp only [restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id,
    Scheme.Modules.Hom.id_app]
  exact M.presheaf.map_id _

/-- Direct restriction and restriction through an intermediate open have the same components. -/
lemma nested_hom_app (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (T : V.toScheme.Opens) :
    (nested M h).hom.app T = M.presheaf.map
      (eqToHom (show U.ι ''ᵁ (X.homOfLE h ''ᵁ T) = V.ι ''ᵁ T by
        simp only [← Scheme.Hom.comp_image, X.homOfLE_ι])).op := by
  simp [nested, Scheme.Modules.Hom.comp_app, ← Functor.map_comp]

attribute [local irreducible] nested inclusionComp

/-- A restricted morphism acts by its original component on the image open. -/
lemma restrict_map_app {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {M N : X.Modules} (a : M ⟶ N) (T : Y.Opens) :
    ((restrictFunctor f).map a).app T = a.app (f ''ᵁ T) := rfl

/-- Restriction through three nested opens is independent of the intermediate path. -/
lemma nested_comp (M : X.Modules) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) :
    nested M (k.trans h) ≪≫ (inclusionComp h k).app (M.restrict U.ι) =
      nested M k ≪≫ (restrictFunctor (X.homOfLE k)).mapIso (nested M h) := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Scheme.Modules.Hom.comp_app,
    restrict_map_app, nested_hom_app, inclusionComp, NatTrans.comp_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app]
  simp only [Scheme.Modules.restrict_map, ← M.presheaf.map_comp]
  congr 1

open ModuleGlobalEvaluationPullback

/-- Free restriction coordinates respect equality of the underlying scheme maps. -/
lemma freeRestrictIso_congr {Y : Scheme.{u}} {f g : Y ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) (ι : Type u) :
    (restrictFunctorCongr h).hom.app (SheafOfModules.free ι) ≫
      (freeRestrictIso g ι).hom = (freeRestrictIso f ι).hom := by
  subst g
  rw [congr_refl, Category.id_comp]

/-- Free coordinates respect the normalized composition of inclusions. -/
lemma free_inclusionComp {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (ι : Type u) :
    (inclusionComp h k).hom.app (SheafOfModules.free ι) ≫
      (restrictFunctor (X.homOfLE k)).map (freeRestrictIso (X.homOfLE h) ι).hom ≫
        (freeRestrictIso (X.homOfLE k) ι).hom =
          (freeRestrictIso (X.homOfLE (k.trans h)) ι).hom := by
  unfold inclusionComp
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, freeRestrictIso_comp, freeRestrictIso_congr]

end FLT.Mazur.OpenModuleRestrictionCoherence
