/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalHomRefinement
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Local maps of normalized pullbacks

Image-open morphisms preserve composition. Normalizing the ambient map of
a refined open immersion does not change its sectionwise restriction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

open ModuleSheafMorphismGluing SheafPullbackMapNormalization

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {M N P : X.Modules}

/-- Extension of restriction maps preserves composition. -/
lemma ofRestriction_comp
    (a : (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N)
    (b : (restrictFunctor i).obj N ⟶ (restrictFunctor i).obj P) :
    ofRestriction i (a ≫ b) = ofRestriction i a ≫ ofRestriction i b := by
  simp only [ofRestriction, Functor.map_comp, SheafOfModules.Hom.over,
    Category.assoc, IsIso.inv_hom_id_assoc]

/-- Changing from pullback to restriction maps preserves composition. -/
lemma toRestriction_comp
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (b : (pullback i).obj N ⟶ (pullback i).obj P) :
    toRestriction i (a ≫ b) = toRestriction i a ≫ toRestriction i b := by
  simp only [toRestriction, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Extending pullback maps to the image open preserves composition. -/
lemma localHom_comp
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (b : (pullback i).obj N ⟶ (pullback i).obj P) :
    localHom i (a ≫ b) = localHom i a ≫ localHom i b := by
  rw [localHom, toRestriction_comp, ofRestriction_comp]
  rfl

/-- A normalized refinement has image contained in the original image. -/
lemma normalizedRange_le (t : Z ⟶ Y) [IsOpenImmersion t]
    (r : Z ⟶ X) [IsOpenImmersion r] (h : t ≫ i = r) :
    r.opensRange ≤ i.opensRange := by
  subst r
  exact refinementRange_le i t

/-- Normalized pullback refinement restricts the same local map on every subopen. -/
lemma localHom_normalize_app (t : Z ⟶ Y) [IsOpenImmersion t]
    (r : Z ⟶ X) [IsOpenImmersion r] (h : t ≫ i = r)
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (T : X.Opens) (hT : T ≤ r.opensRange) :
    localApp (localHom r (normalize t i i r r h h a)) hT =
      localApp (localHom i a) (hT.trans (normalizedRange_le i t r h)) := by
  subst r
  simpa only [SheafPullbackMapNormalization.normalize, SheafPullbackPathComparison.comparison,
    Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, pullbackCongr,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id] using localHom_refine_app i t a T hT

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
