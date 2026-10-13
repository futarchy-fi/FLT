/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterTranslationBaseChange
public import FLT.Mazur.PolygonParameterMarkingLine
public import FLT.Mazur.RelativeCartierBaseChangeComposition

/-!
# Successive base change of arbitrary translated polygon markings

The composition chart preserves the full moved Cartier ideal. Its positive-line
comparison therefore preserves the canonical marking section without rescaling.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T U : Scheme} (g : T ⟶ Spec (.of K)) (k : U ⟶ T)
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Kˣ) (i : Fin n)
local notation "H" => Over.pullback k
local notation "δ" => NatTrans.app (Iso.inv (Over.pullbackComp k g)) C
local notation "π" => (pullback.fst (pullback.snd C.hom g) k)

/-- The composition chart also intertwines the original inverse translations. -/
theorem translationIso_baseChange_inv :
    (H).map (translationIso K n hn p q h g c).inv ≫ δ =
      δ ≫ (translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c)).inv := by
  apply (Iso.eq_comp_inv _).2
  have ht := translation_baseChange K n hn p q h g k c
  rw [← translationIso_hom, ← translationIso_hom] at ht
  rw [Category.assoc, ← ht, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, (H).map_id, Category.id_comp]

/-- The actual comparison preserves the complete translated ideal after successive pullback. -/
theorem movedMarkingIdeal_baseChange :
    (movedMarkingIdeal K n hn p q h (k ≫ g) (parameterBaseChange K n g k c) a i).comap
      (δ).left = (movedMarkingIdeal K n hn p q h g c a i).comap π := by
  have ht := congrArg Over.Hom.left (translationIso_baseChange_inv K n hn p q h g k c)
  dsimp only [Over.comp_left] at ht
  simp only [movedMarkingIdeal, markingIdeal, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  rw [← Category.assoc, ← ht, Category.assoc, OverPullbackSection.comp_inv_fst,
    ← Category.assoc, ← Category.assoc]
  congr 1
  simp only [Over.pullback_map_left, pullback.lift_fst]
  rfl

/-- The moved positive-line comparison on the actual iterated pullback chart. -/
irreducible_def movedMarkingBaseChangeLineIso :
    (Scheme.Modules.pullback (δ).left).obj
      (movedMarkingLine K n hn p q h (k ≫ g) (parameterBaseChange K n g k c) a i) ≅
        divisorLineBundle ((movedMarkingIdeal K n hn p q h g c a i).comap π)
          (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
            (movedMarkingIdeal_cartier K n hn p q h g c a i)).1 := by
  let hs := (movedMarkingIdeal_cartier K n hn p q h (k ≫ g)
    (parameterBaseChange K n g k c) a i).1
  let ht := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (movedMarkingIdeal_cartier K n hn p q h g c a i)).1
  let he := movedMarkingIdeal_baseChange K n hn p q h g k c a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- Successive arbitrary base change preserves the moved marking's canonical section exactly. -/
theorem movedMarkingBaseChangeLineIso_section :
    DivisorLineSectionCompatible (δ).left
      (movedMarkingIdeal_cartier K n hn p q h (k ≫ g)
        (parameterBaseChange K n g k c) a i).1
      (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
        (movedMarkingIdeal_cartier K n hn p q h g c a i)).1
      (movedMarkingBaseChangeLineIso K n hn p q h g k c a i) := by
  let hs := (movedMarkingIdeal_cartier K n hn p q h (k ≫ g)
    (parameterBaseChange K n g k c) a i).1
  let ht := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (movedMarkingIdeal_cartier K n hn p q h g c a i)).1
  let he := movedMarkingIdeal_baseChange K n hn p q h g k c a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [movedMarkingBaseChangeLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonParameterTranslation
