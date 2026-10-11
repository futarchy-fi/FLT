/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingBaseChange

/-!
# Composition of actual group-scheme base changes

The canonical pullback comparison lifts to the constructed commutative group
objects. It retains the original comparison of schemes over the source base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S) (G : CommGrp (Over S))

/-- Iterated pullback and pullback along the composite have the same actual group object. -/
def compIso : (Over.pullback (f ≫ g)).mapCommGrp.obj G ≅
    (Over.pullback f).mapCommGrp.obj ((Over.pullback g).mapCommGrp.obj G) :=
  (Functor.mapCommGrpNatIso (Over.pullbackComp f g)).app G ≪≫
    (Functor.mapCommGrpCompIso (F := Over.pullback g) (G := Over.pullback f)).app G

/-- The group comparison retains the original canonical map of pullback schemes. -/
theorem compIso_hom :
    (compIso f g G).hom.hom.hom.hom = (Over.pullbackComp f g).hom.app G.X := by
  change (Over.pullbackComp f g).hom.app G.X ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The inverse group comparison retains the original inverse pullback map. -/
theorem compIso_inv :
    (compIso f g G).inv.hom.hom.hom = (Over.pullbackComp f g).inv.app G.X := by
  change 𝟙 _ ≫ (Over.pullbackComp f g).inv.app G.X = _
  exact Category.id_comp _

/-- Equality of actual base morphisms gives equality transport of their group pullbacks. -/
def congrIso {f g : T ⟶ S} (h : f = g) (G : CommGrp (Over S)) :
    (Over.pullback f).mapCommGrp.obj G ≅ (Over.pullback g).mapCommGrp.obj G :=
  eqToIso (congrArg (fun k => (Over.pullback k).mapCommGrp.obj G) h)

/-- Forgetting the group structure retains equality transport of the original schemes. -/
theorem congrIso_hom {f g : T ⟶ S} (h : f = g) (G : CommGrp (Over S)) :
    (congrIso h G).hom.hom.hom.hom =
      eqToHom (congrArg (fun k => (Over.pullback k).obj G.X) h) := by
  subst g
  rfl

end FLT.Mazur.GroupSchemeBaseChange
