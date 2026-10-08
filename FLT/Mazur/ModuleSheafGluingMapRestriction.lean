/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluing

/-!
# Recovery of glued morphisms on the original charts

The projection equation and counit naturality show that a glued morphism
restricts to each original chart morphism under the recovery isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafGluing.Data.Map
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
variable {D E : Data U} (a : D.Map E)

/-- Recovering the glued morphism on a chart gives its original chart map. -/
@[reassoc]
lemma gluedMap_restrictionIso (hU : iSup U = ⊤) (i : ι) :
    (restrictFunctor (U i).ι).map (a.gluedMap hU) ≫ (E.restrictionIso i).hom =
      (D.restrictionIso i).hom ≫ a.app i := by
  have hp := congrArg ((restrictFunctor (U i).ι).map)
    (a.gluedMap_projection hU i)
  rw [Functor.map_comp, Functor.map_comp] at hp
  have hc := (restrictFunctorAdjCounitIso (U i).ι).hom.naturality (a.app i)
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  simp only [Data.restrictionIso, Iso.trans_hom, asIso_hom, Iso.app_hom]
  rw [← Category.assoc, hp, Category.assoc, hc, Category.assoc]

end FLT.Mazur.ModuleSheafGluing.Data.Map
