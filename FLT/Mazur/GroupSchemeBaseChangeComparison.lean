/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSchemeBaseChangeProjections

/-!
# Coefficient comparisons retain arbitrary-source sections

A coefficient group isomorphism, pulled back and composed with the canonical
base-change comparisons, retains the original coefficient projection. The
formula is abstract in the group objects, so concrete group laws stay sealed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S) (k : U ⟶ S)
  (h : f ≫ g = k) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  (e : H ≅ (Over.pullback g).mapCommGrp.obj G)

/-- A coefficient comparison on an arbitrary source retains its original family projection. -/
@[reassoc] theorem coefficientComparison_fst :
    (((Over.pullback f).mapCommGrp.mapIso e ≪≫ (compIso f g G).symm ≪≫
      congrIso h G).hom.hom.hom.hom.left) ≫ pullback.fst G.X.hom k =
        pullback.fst H.X.hom f ≫ e.hom.hom.hom.hom.left ≫ pullback.fst G.X.hom g := by
  change (((Over.pullback f).mapCommGrp.map e.hom).hom.hom.hom.left ≫
    (compIso f g G).inv.hom.hom.hom.left ≫ (congrIso h G).hom.hom.hom.hom.left) ≫ _ = _
  rw [Category.assoc, Category.assoc, congrIso_hom_fst, compIso_inv_fst,
    ← Category.assoc]
  exact (congrArg (fun z => z ≫ pullback.fst G.X.hom g)
    (map_hom_fst f e.hom)).trans (Category.assoc _ _ _)

/-- Pulling back a group morphism commutes with the full marking adjunction. -/
theorem pointsMulEquiv_map {A B : CommGrp (Over T)} (e : A ⟶ B) (V : Over U)
    (p : (Over.map f).obj V ⟶ A.X) :
    GroupMarkingBaseChange.pointsMulEquiv f A.X V p ≫
      ((Over.pullback f).mapCommGrp.map e).hom.hom.hom =
        GroupMarkingBaseChange.pointsMulEquiv f B.X V (p ≫ e.hom.hom.hom) :=
  ((Over.mapPullbackAdj f).homEquiv_naturality_right p e.hom.hom.hom).symm

end FLT.Mazur.GroupSchemeBaseChange
