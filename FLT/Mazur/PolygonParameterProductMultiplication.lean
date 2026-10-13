/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductLine
public import FLT.Mazur.PolygonParameterMarkingMultiplication
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# Multiplication coherence for full polygon product markings

Translation by a second arbitrary group section carries the first full product marking
to the full marking for the product section. The actual positive lines and canonical
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
  (c d : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Fin n → Kˣ)

/-- The second translation pulls the full product marking back to the first moved product. -/
theorem movedProductMarkingIdeal_mul_pullback :
    (movedProductMarkingIdeal K n hn p q h g (d * c) a).comap
      (translationIso K n hn p q h g d).hom.left =
        movedProductMarkingIdeal K n hn p q h g c a := by
  simp only [movedProductMarkingIdeal, idealSheaf_comap_prod,
    movedMarkingIdeal_mul_pullback]

/-- Positive-line comparison from the product marking to the first moved marking. -/
irreducible_def movedProductMarkingMulLineIso :
    (Scheme.Modules.pullback (translationIso K n hn p q h g d).hom.left).obj
      (movedProductMarkingLine K n hn p q h g (d * c) a) ≅
        movedProductMarkingLine K n hn p q h g c a := by
  let hs := (movedProductMarkingIdeal_cartier K n hn p q h g (d * c) a).1
  let ht := (movedProductMarkingIdeal_cartier K n hn p q h g c a).1
  let he := movedProductMarkingIdeal_mul_pullback K n hn p q h g c d a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The multiplication comparison retains the original canonical vanishing sections. -/
theorem movedProductMarkingMulLineIso_section :
    DivisorLineSectionCompatible (translationIso K n hn p q h g d).hom.left
      (movedProductMarkingIdeal_cartier K n hn p q h g (d * c) a).1
      (movedProductMarkingIdeal_cartier K n hn p q h g c a).1
      (movedProductMarkingMulLineIso K n hn p q h g c d a) := by
  let hs := (movedProductMarkingIdeal_cartier K n hn p q h g (d * c) a).1
  let ht := (movedProductMarkingIdeal_cartier K n hn p q h g c a).1
  let he := movedProductMarkingIdeal_mul_pullback K n hn p q h g c d a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [movedProductMarkingMulLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Two successive varying translations satisfy the actual marking-line cocycle. -/
theorem movedProductMarkingLineIso_mul_triangle :
    LinePullbackTriangle (translationIso K n hn p q h g c).hom.left
      (translationIso K n hn p q h g d).hom.left
      (translationIso K n hn p q h g (d * c)).hom.left
      (translationIso_mul_hom K n hn p q h g c d)
      (movedProductMarkingMulLineIso K n hn p q h g c d a)
      (movedProductMarkingLineIso K n hn p q h g c a)
      (movedProductMarkingLineIso K n hn p q h g (d * c) a) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (movedProductMarkingMulLineIso_section K n hn p q h g c d a)
    (movedProductMarkingLineIso_section K n hn p q h g c a)
    (movedProductMarkingLineIso_section K n hn p q h g (d * c) a)

end FLT.Mazur.PolygonParameterTranslation
