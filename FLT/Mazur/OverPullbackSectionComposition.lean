/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackSection
public import FLT.Mazur.OverPullbackCoherence

/-!
# Sections under composed scheme pullback

The inverse canonical comparison retains both original family projections.
Together with projection uniqueness this identifies iterated lifts with lifts
along the composite base map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OverPullbackSection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S) (G : Over S)

/-- The inverse canonical comparison projects through the two original families. -/
@[reassoc] theorem comp_inv_fst :
    ((Over.pullbackComp f g).inv.app G).left ≫ pullback.fst G.hom (f ≫ g) =
      pullback.fst ((Over.pullback g).obj G).hom f ≫ pullback.fst G.hom g := by
  rw [← OverPullbackCoherence.comp_left_fst_fst g f G, ← Category.assoc]
  have h := congrArg Over.Hom.left ((Over.pullbackComp f g).inv_hom_id_app G)
  change ((Over.pullbackComp f g).inv.app G).left ≫
    ((Over.pullbackComp f g).hom.app G).left = 𝟙 _ at h
  rw [h, Category.id_comp]
  rfl

/-- Iterated relative points compare with the actual section over the composite base. -/
theorem lift_comp (p : Over.mk f ⟶ (Over.pullback g).obj G)
    (q : Over.mk (f ≫ g) ⟶ G)
    (h : p.left ≫ pullback.fst G.hom g = q.left) :
    lift f ((Over.pullback g).obj G) p ≫ (Over.pullbackComp f g).inv.app G =
      lift (f ≫ g) G q := by
  apply hom_ext
  rw [Over.comp_left, Category.assoc, comp_inv_fst, ← Category.assoc,
    lift_fst, h, lift_fst]

end FLT.Mazur.OverPullbackSection
