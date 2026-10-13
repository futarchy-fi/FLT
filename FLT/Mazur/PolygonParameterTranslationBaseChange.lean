/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonoidalActionSpecialization
public import FLT.Mazur.PolygonParameterTranslation

/-!
# Varying polygon translations under successive base changes

An arbitrary group section over the first parameter scheme pulls back to the
composite parameter scheme. Its actual whole-polygon translation commutes with
the canonical comparison of iterated and composite fiber products.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonActionBaseChange
open MonoidalActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T U : Scheme.{u}} (g : T ⟶ Spec (.of K)) (k : U ⟶ T)
local notation "F" => Over.pullback g
local notation "H" => Over.pullback k

/-- Pull an arbitrary parameter section back to the actual composite base change. -/
def parameterBaseChange (c : 𝟙_ (Over T) ⟶ (F).obj (G K n)) :
    𝟙_ (Over U) ⟶ (Over.pullback (k ≫ g)).obj (G K n) :=
  Functor.LaxMonoidal.ε (H) ≫ (H).map c ≫ (Over.pullbackComp k g).inv.app (G K n)

/-- The original comparison intertwines translations after arbitrary successive base changes. -/
theorem translation_baseChange (c : 𝟙_ (Over T) ⟶ (F).obj (G K n)) :
    (H).map (translation K n hn p q h g c) ≫ (Over.pullbackComp k g).inv.app C =
      (Over.pullbackComp k g).inv.app C ≫
        translation K n hn p q h (k ≫ g) (parameterBaseChange K n g k c) := by
  have hm := map_specialize (H) (baseChangedAct K n hn p q h g) c
  have he := specialize_naturality ((F) ⋙ (H)) (Over.pullback (k ≫ g))
    (Over.pullbackComp k g).inv (act K n hn p q h)
    (Functor.LaxMonoidal.ε (H) ≫ (H).map c)
  dsimp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Functor.comp_map] at he
  change _ = (H).map (translation K n hn p q h g c) at hm
  rw [← hm]
  simpa only [baseChangedAct, Functor.map_comp, Category.assoc,
    specialize, parameterBaseChange, translation] using he

/-- The full translation isomorphism, including its inverse, respects the composition chart. -/
theorem translationIso_baseChange (c : 𝟙_ (Over T) ⟶ (F).obj (G K n)) :
    (H).mapIso (translationIso K n hn p q h g c) ≪≫
        (Over.pullbackComp k g).symm.app C =
      (Over.pullbackComp k g).symm.app C ≪≫
        translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    translationIso_hom] using translation_baseChange K n hn p q h g k c

end FLT.Mazur.PolygonParameterTranslation
