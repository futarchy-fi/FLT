/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationRingedCofork

/-!
# Descent into the ringed orbit space

A ringed cofork supplies compatible regular functions on the source. These
factor through the invariant sheaf after descending its underlying continuous map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)
  (s : Cofork p.left.toShHom q.left.toShHom)

/-- The continuous map descending any ringed cofork to the orbit space. -/
def ringedDescendBase : space e ⟶ s.pt.carrier :=
  (orbitCoforkIsColimit e).desc
    (Cofork.ofπ s.π.hom.base (congrArg (fun k ↦ k.hom.base) s.condition))

/-- The descended continuous map factors the source map. -/
theorem ringedDescendBase_fac : quotientMap e ≫ ringedDescendBase e s = s.π.hom.base :=
  Cofork.IsColimit.π_desc (orbitCoforkIsColimit e)

/-- The source regular-function map on the descended open domains. -/
def ringedDescendSource : s.pt.presheaf ⟶
    (TopCat.Presheaf.pushforward _ (ringedDescendBase e s)).obj (sourceSheaf e).obj :=
  s.π.hom.c ≫ (TopCat.Presheaf.pushforwardEq
    (ringedDescendBase_fac e s).symm U.left.presheaf).hom

/-- The descended source functions satisfy the original relation. -/
theorem ringedDescendSource_condition :
    ringedDescendSource e s ≫ (TopCat.Presheaf.pushforward _ (ringedDescendBase e s)).map
      (firstRestriction e).hom =
    ringedDescendSource e s ≫ (TopCat.Presheaf.pushforward _ (ringedDescendBase e s)).map
      (secondRestriction e).hom := by
  apply NatTrans.ext
  funext W
  have h := PresheafedSpace.congr_app
    (congrArg (fun k ↦ k.hom) s.condition) W
  change s.π.hom.c.app W ≫ p.left.toPshHom.c.app _ =
    (s.π.hom.c.app W ≫ q.left.toPshHom.c.app _) ≫
      A.left.presheaf.map (eqToHom _) at h
  dsimp [ringedDescendSource, firstRestriction, secondRestriction]
  simp only [TopCat.Presheaf.pushforwardEq_hom_app]
  rw [Category.assoc]
  erw [p.left.toPshHom.c.naturality]
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  erw [q.left.toPshHom.c.naturality_assoc]
  simp only [TopCat.Presheaf.pushforward_obj_map, ← Functor.map_comp]
  congr 2

/-- The morphism of ringed spaces descending an arbitrary actual relation cofork. -/
def ringedDescend : ringedSpace e ⟶ s.pt :=
  ⟨ringedDescendBase e s, (pushInvariantIsLimit e (ringedDescendBase e s)).lift
    (Fork.ofι (ringedDescendSource e s) (ringedDescendSource_condition e s))⟩

/-- The descended ringed morphism recovers the original source map. -/
theorem ringedDescend_fac : toRingedSpace e ≫ ringedDescend e s = s.π := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  apply PresheafedSpace.hext ((toRingedSpace e ≫ ringedDescend e s).hom)
    s.π.hom (ringedDescendBase_fac e s)
  have h := Fork.IsLimit.lift_ι (pushInvariantIsLimit e (ringedDescendBase e s))
    (t := Fork.ofι (ringedDescendSource e s) (ringedDescendSource_condition e s))
  exact (heq_of_eq h).trans
    (pushforwardEq_comp_heq (ringedDescendBase_fac e s).symm U.left.presheaf s.π.hom.c)

end FLT.Mazur.RelativeRelationOrbit
