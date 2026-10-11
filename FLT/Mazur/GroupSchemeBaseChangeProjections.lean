/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSchemeBaseChangeComposition
public import FLT.Mazur.OverPullbackCoherence

/-!
# Projection equations for group-scheme base change

The group comparison maps retain the canonical projections of the underlying
schemes. These equations allow marked sections to be compared without unfolding
any geometric group law.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S) (G : CommGrp (Over S))

/-- The composite group pullback comparison retains the original family projection. -/
@[reassoc] theorem compIso_hom_fst_fst :
    (compIso f g G).hom.hom.hom.hom.left ≫
      pullback.fst ((Over.pullback g).obj G.X).hom f ≫ pullback.fst G.X.hom g =
        pullback.fst G.X.hom (f ≫ g) := by
  rw [compIso_hom]
  exact OverPullbackCoherence.comp_left_fst_fst g f G.X

/-- The inverse comparison projects through the two original pullbacks. -/
@[reassoc] theorem compIso_inv_fst :
    (compIso f g G).inv.hom.hom.hom.left ≫ pullback.fst G.X.hom (f ≫ g) =
      pullback.fst ((Over.pullback g).obj G.X).hom f ≫ pullback.fst G.X.hom g := by
  rw [← compIso_hom_fst_fst f g G, ← Category.assoc]
  have h := congrArg (fun k => k.hom.hom.hom.left) (compIso f g G).inv_hom_id
  change (compIso f g G).inv.hom.hom.hom.left ≫
    (compIso f g G).hom.hom.hom.hom.left = 𝟙 _ at h
  rw [h, Category.id_comp]

/-- Equality transport of base maps retains the original projection. -/
@[reassoc] theorem congrIso_hom_fst {f g : T ⟶ S} (h : f = g) (G : CommGrp (Over S)) :
    (congrIso h G).hom.hom.hom.hom.left ≫ pullback.fst G.X.hom g =
      pullback.fst G.X.hom f := by
  subst g
  exact Category.id_comp _

/-- A pulled-back group morphism retains its actual original family map. -/
@[reassoc] theorem map_hom_fst {G H : CommGrp (Over S)} (e : G ⟶ H) :
    ((Over.pullback g).mapCommGrp.map e).hom.hom.hom.left ≫ pullback.fst H.X.hom g =
      pullback.fst G.X.hom g ≫ e.hom.hom.hom.left := by
  change ((Over.pullback g).map e.hom.hom.hom).left ≫ _ = _
  simp only [Over.pullback_map_left, pullback.lift_fst]

end FLT.Mazur.GroupSchemeBaseChange
