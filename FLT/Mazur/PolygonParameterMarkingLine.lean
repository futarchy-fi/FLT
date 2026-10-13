/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterTranslation
public import FLT.Mazur.PolygonMarkingBaseChange
public import FLT.Mazur.CartierIdealPullbackComparison

/-!
# Marking lines under translations by varying parameter sections

Transport the full original marking ideal by an arbitrary section of the
base-changed group. It stays relative Cartier, and its positive-line comparison
preserves the canonical vanishing section on the entire polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Kˣ) (i : Fin n)

/-- The full original marking ideal translated by an arbitrary varying group section. -/
def movedMarkingIdeal : ((Over.pullback g).obj C).left.IdealSheafData :=
  (markingIdeal K n p g a i).comap (translationIso K n hn p q h g c).inv.left

/-- Translation preserves relative Cartierness over the actual parameter scheme. -/
theorem movedMarkingIdeal_cartier :
    RelativeEffectiveCartier ((Over.pullback g).obj C).hom
      (movedMarkingIdeal K n hn p q h g c a i) := by
  let e := (Over.forget T).mapIso (translationIso K n hn p q h g c)
  have hc := (markingIdeal_cartier K n hn p q h g a i).comap_of_isOpenImmersion e.inv
  change RelativeEffectiveCartier
    ((translationIso K n hn p q h g c).inv.left ≫ ((Over.pullback g).obj C).hom)
    ((markingIdeal K n p g a i).comap (translationIso K n hn p q h g c).inv.left) at hc
  rw [Over.w] at hc
  exact hc

/-- Pulling the translated full ideal back by its translation returns the original ideal. -/
theorem movedMarkingIdeal_pullback :
    (movedMarkingIdeal K n hn p q h g c a i).comap
      (translationIso K n hn p q h g c).hom.left = markingIdeal K n p g a i := by
  rw [movedMarkingIdeal, ← Scheme.IdealSheafData.comap_comp]
  have he := congrArg Over.Hom.left (translationIso K n hn p q h g c).hom_inv_id
  change (translationIso K n hn p q h g c).hom.left ≫
    (translationIso K n hn p q h g c).inv.left = 𝟙 _ at he
  rw [he, Scheme.IdealSheafData.comap_id]

/-- The actual positive line of the translated marking. -/
def movedMarkingLine : ((Over.pullback g).obj C).left.Modules :=
  divisorLineBundle (movedMarkingIdeal K n hn p q h g c a i)
    (movedMarkingIdeal_cartier K n hn p q h g c a i).1

/-- The full translation compares the moved positive marking line with the original line. -/
irreducible_def movedMarkingLineIso :
    (Scheme.Modules.pullback (translationIso K n hn p q h g c).hom.left).obj
      (movedMarkingLine K n hn p q h g c a i) ≅ markingLine K n hn p q h g a i := by
  let hs := (movedMarkingIdeal_cartier K n hn p q h g c a i).1
  let ht := (markingIdeal_cartier K n hn p q h g a i).1
  let he := movedMarkingIdeal_pullback K n hn p q h g c a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- Varying translations retain the actual canonical marking section. -/
theorem movedMarkingLineIso_section :
    DivisorLineSectionCompatible (translationIso K n hn p q h g c).hom.left
      (movedMarkingIdeal_cartier K n hn p q h g c a i).1
      (markingIdeal_cartier K n hn p q h g a i).1
      (movedMarkingLineIso K n hn p q h g c a i) := by
  let hs := (movedMarkingIdeal_cartier K n hn p q h g c a i).1
  let ht := (markingIdeal_cartier K n hn p q h g a i).1
  let he := movedMarkingIdeal_pullback K n hn p q h g c a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [movedMarkingLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonParameterTranslation
