/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionAssociativity

/-!
# Whole-polygon actions respect normalization comparisons

A map preserving the specified normalization commutes with the descended
whole-polygon action. Evaluating at any group section preserves the same
comparison, so field-coordinate identifications retain actual translations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonActionCoconeNaturality
open PolygonPinching PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (hm : 0 < m)
  {C D : Over (Spec (.of K))}
  (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (p' : components K m ⟶ D) (q' : nodes K m ⟶ D)
  (h' : IsPushout (toComponents K m hm) (toNodes K m) p' q')
  (d : C ⟶ D) (hp : p ≫ d = p')

include hp in
/-- Normalization-preserving maps intertwine the full descended polygon actions. -/
@[reassoc] theorem action_natural :
    act K m hm p q h ≫ d = G K m ◁ d ≫ act K m hm p' q' h' := by
  let _ : Epi (G K m ◁ p) :=
    PolygonActionAssociativity.tensor_normalization_epi K m hm p q h _
  apply (cancel_epi (G K m ◁ p)).mp
  apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod m ↦ gm K)
    (fun _ : Fin m ↦ component K)
  intro b i
  change (PolygonSplitGroup.component K m b ⊗ₘ componentι K m i) ≫ _ = _
  rw [tensorHom_comp_whiskerLeft_assoc, tensorHom_comp_whiskerLeft_assoc,
    tensorHom_comp_whiskerLeft_assoc, Category.assoc, hp,
    component_act_assoc]
  erw [component_act K m hm p' q' h' b i]
  rw [hp]

include hp in
/-- Evaluating at a section retains the original normalization comparison. -/
@[reassoc] theorem translation_natural (c : 𝟙_ (Over (Spec (.of K))) ⟶ G K m) :
    ((λ_ C).inv ≫ c ▷ C ≫ act K m hm p q h) ≫ d =
      d ≫ (λ_ D).inv ≫ c ▷ D ≫ act K m hm p' q' h' := by
  rw [Category.assoc, Category.assoc, action_natural K m hm p q h p' q' h' d hp,
    ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

end FLT.Mazur.PolygonActionCoconeNaturality
