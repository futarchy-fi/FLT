/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterTranslation
public import FLT.Mazur.PolygonActionTranslation

/-!
# Original translations inside the varying-parameter action

Pulling back an original group point and then evaluating the full action
is exactly the pullback of the original whole-polygon translation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonActionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme.{u}} (g : T ⟶ Spec (.of K))
local notation "F" => Over.pullback g

/-- The original field-valued parameter regarded as a section over an arbitrary new base. -/
def originalParameter (a : Kˣ) (b : ZMod n) : 𝟙_ (Over T) ⟶ (F).obj (G K n) :=
  Functor.LaxMonoidal.ε (F) ≫ (F).map (PolygonActionTranslation.groupPoint K n a b)

/-- Evaluation of the pulled-back parameter is exactly the original pulled-back translation. -/
theorem translation_originalParameter (a : Kˣ) (b : ZMod n) :
    translation K n hn p q h g (originalParameter K n g a b) =
      (F).map (PolygonActionTranslation.translation K n hn p q h a b) := by
  simp only [translation, originalParameter, baseChangedAct,
    PolygonActionTranslation.translation, Functor.map_comp, comp_whiskerRight, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [Functor.LaxMonoidal.left_unitality_inv_assoc]

/-- The parameter automorphism's underlying map retains the original full translation. -/
theorem translationIso_originalParameter_hom (a : Kˣ) (b : ZMod n) :
    (translationIso K n hn p q h g (originalParameter K n g a b)).hom =
      (F).map (PolygonActionTranslation.translation K n hn p q h a b) := by
  rw [translationIso_hom, translation_originalParameter]

end FLT.Mazur.PolygonParameterTranslation
