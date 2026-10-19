/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRingedCofork

/-!
# Descent into the ringed orbit space

A ringed cofork supplies compatible regular functions on the source. These
factor through the invariant sheaf after descending its underlying continuous map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n
variable (s : Cofork (disjointComparisonSource n).toShHom
  (disjointComparisonTarget n).toShHom)

/-- The continuous map descending any ringed cofork to the orbit space. -/
def ringedDescendBase : space n ⟶ s.pt.carrier :=
  (orbitCoforkIsColimit n).desc
    (Cofork.ofπ s.π.hom.base (congrArg (fun k ↦ k.hom.base) s.condition))

/-- The descended continuous map factors the source map. -/
theorem ringedDescendBase_fac : quotientMap n ≫ ringedDescendBase n s = s.π.hom.base :=
  Cofork.IsColimit.π_desc (orbitCoforkIsColimit n)

/-- The source regular-function map on the descended open domains. -/
def ringedDescendSource : s.pt.presheaf ⟶
    (TopCat.Presheaf.pushforward _ (ringedDescendBase n s)).obj (sourceSheaf n).obj :=
  s.π.hom.c ≫ (TopCat.Presheaf.pushforwardEq
    (ringedDescendBase_fac n s).symm (U).presheaf).hom

/-- The descended source functions satisfy the original relation. -/
theorem ringedDescendSource_condition :
    ringedDescendSource n s ≫ (TopCat.Presheaf.pushforward _ (ringedDescendBase n s)).map
      (firstRestriction n).hom =
    ringedDescendSource n s ≫ (TopCat.Presheaf.pushforward _ (ringedDescendBase n s)).map
      (secondRestriction n).hom := by
  apply NatTrans.ext
  funext W
  have h := PresheafedSpace.congr_app
    (congrArg (fun k ↦ k.hom) s.condition) W
  change s.π.hom.c.app W ≫ (src).toPshHom.c.app _ =
    (s.π.hom.c.app W ≫ (tgt).toPshHom.c.app _) ≫
      (A).presheaf.map (eqToHom _) at h
  dsimp [ringedDescendSource, firstRestriction, secondRestriction]
  simp only [TopCat.Presheaf.pushforwardEq_hom_app]
  rw [Category.assoc]
  erw [(src).toPshHom.c.naturality]
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  erw [(tgt).toPshHom.c.naturality_assoc]
  simp only [TopCat.Presheaf.pushforward_obj_map, ← Functor.map_comp]
  congr 2

/-- The morphism of ringed spaces descending an arbitrary actual relation cofork. -/
def ringedDescend : ringedSpace n ⟶ s.pt :=
  ⟨ringedDescendBase n s, (pushInvariantIsLimit n (ringedDescendBase n s)).lift
    (Fork.ofι (ringedDescendSource n s) (ringedDescendSource_condition n s))⟩

/-- The descended ringed morphism recovers the original source map. -/
theorem ringedDescend_fac : toRingedSpace n ≫ ringedDescend n s = s.π := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  apply PresheafedSpace.hext ((toRingedSpace n ≫ ringedDescend n s).hom)
    s.π.hom (ringedDescendBase_fac n s)
  have h := Fork.IsLimit.lift_ι (pushInvariantIsLimit n (ringedDescendBase n s))
    (t := Fork.ofι (ringedDescendSource n s) (ringedDescendSource_condition n s))
  exact (heq_of_eq h).trans
    (pushforwardEq_comp_heq (ringedDescendBase_fac n s).symm (U).presheaf s.π.hom.c)

end FLT.Mazur.CyclicCharacteristicOrbit
