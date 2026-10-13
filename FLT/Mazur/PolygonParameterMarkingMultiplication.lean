/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterMarkingLine
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# Multiplication coherence for varying-parameter marking lines

Translation by a second arbitrary group section carries the first moved marking
to the marking for the product section. The actual positive lines and canonical
sections retain the multiplication triangle on the entire polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c d : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Kˣ) (i : Fin n)

/-- Multiplication of arbitrary sections retains the original automorphism composition. -/
theorem translationIso_mul_hom :
    (translationIso K n hn p q h g c).hom.left ≫
      (translationIso K n hn p q h g d).hom.left =
        (translationIso K n hn p q h g (d * c)).hom.left := by
  have he := translation_comp K n hn p q h g c d
  rw [← translationIso_hom, ← translationIso_hom, ← translationIso_hom] at he
  exact congrArg Over.Hom.left he

/-- The second translation pulls the product marking back to the first moved marking. -/
theorem movedMarkingIdeal_mul_pullback :
    (movedMarkingIdeal K n hn p q h g (d * c) a i).comap
      (translationIso K n hn p q h g d).hom.left =
        movedMarkingIdeal K n hn p q h g c a i := by
  have he' : (translationIso K n hn p q h g d).hom ≫
      (translationIso K n hn p q h g (d * c)).inv =
        (translationIso K n hn p q h g c).inv := by
    rw [Iso.comp_inv_eq, Iso.eq_inv_comp]
    simpa only [translationIso_hom] using translation_comp K n hn p q h g c d
  have he := congrArg Over.Hom.left he'
  dsimp only [Over.comp_left] at he
  rw [movedMarkingIdeal, ← Scheme.IdealSheafData.comap_comp, he, movedMarkingIdeal]

/-- Positive-line comparison from the product marking to the first moved marking. -/
irreducible_def movedMarkingMulLineIso :
    (Scheme.Modules.pullback (translationIso K n hn p q h g d).hom.left).obj
      (movedMarkingLine K n hn p q h g (d * c) a i) ≅
        movedMarkingLine K n hn p q h g c a i := by
  let hs := (movedMarkingIdeal_cartier K n hn p q h g (d * c) a i).1
  let ht := (movedMarkingIdeal_cartier K n hn p q h g c a i).1
  let he := movedMarkingIdeal_mul_pullback K n hn p q h g c d a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The multiplication comparison retains the original canonical vanishing sections. -/
theorem movedMarkingMulLineIso_section :
    DivisorLineSectionCompatible (translationIso K n hn p q h g d).hom.left
      (movedMarkingIdeal_cartier K n hn p q h g (d * c) a i).1
      (movedMarkingIdeal_cartier K n hn p q h g c a i).1
      (movedMarkingMulLineIso K n hn p q h g c d a i) := by
  let hs := (movedMarkingIdeal_cartier K n hn p q h g (d * c) a i).1
  let ht := (movedMarkingIdeal_cartier K n hn p q h g c a i).1
  let he := movedMarkingIdeal_mul_pullback K n hn p q h g c d a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [movedMarkingMulLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Two successive varying translations satisfy the actual marking-line cocycle. -/
theorem movedMarkingLineIso_mul_triangle :
    LinePullbackTriangle (translationIso K n hn p q h g c).hom.left
      (translationIso K n hn p q h g d).hom.left
      (translationIso K n hn p q h g (d * c)).hom.left
      (translationIso_mul_hom K n hn p q h g c d)
      (movedMarkingMulLineIso K n hn p q h g c d a i)
      (movedMarkingLineIso K n hn p q h g c a i)
      (movedMarkingLineIso K n hn p q h g (d * c) a i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (movedMarkingMulLineIso_section K n hn p q h g c d a i)
    (movedMarkingLineIso_section K n hn p q h g c a i)
    (movedMarkingLineIso_section K n hn p q h g (d * c) a i)

end FLT.Mazur.PolygonParameterTranslation
