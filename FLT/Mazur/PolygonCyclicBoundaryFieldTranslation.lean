/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryParameterSections
public import FLT.Mazur.PolygonParameterTranslation
public import FLT.Mazur.PolygonActionFieldExtension

/-!
# Actual boundary translations in extension-field group coordinates

The actual cyclic parameter section is transported through the original split
group comparison. Evaluating the intrinsic extension-field whole-polygon action
then gives exactly the original pulled-back translation. Common finite relabeling
retains this comparison on the original extension-field pinching cocone.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation
open CyclicBoundaryParameter CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n]
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "F" => Over.pullback (g)
variable (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
  CyclicBoundaryParameter.parameter (G K m) n) (j : Multiplicative (ZMod n))
local notation "c" => markedSection (G K m) n (g) f (1, 1, j)
local notation "e" => PolygonActionFieldExtension.groupIso K L m
local notation "pL" => PolygonActionFieldExtension.normalization K L m p
local notation "qL" => PolygonActionFieldExtension.nodeMap K L m q
local notation "hL" => PolygonActionFieldExtension.cocone K L m hm p q h

/-- The actual boundary parameter section in the extension-field split group. -/
def extendedParameter : 𝟙_ (Over (Spec (.of L))) ⟶ G L m := (c) ≫ (e).inv

/-- The field-coordinate section recovers the entire original pulled-back parameter. -/
@[reassoc] theorem extendedParameter_group :
    extendedParameter K L m n f j ≫ (e).hom = (c) := by
  rw [extendedParameter, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Evaluate the intrinsic field-extension action on the original pulled-back whole polygon. -/
def extendedTranslation : (F).obj C ⟶ (F).obj C :=
  (λ_ ((F).obj C)).inv ≫ extendedParameter K L m n f j ▷ (F).obj C ≫
    act L m hm (pL) (qL) (hL)

/-- Intrinsic extension-field translation is the actual original base-changed translation. -/
theorem extendedTranslation_eq :
    extendedTranslation K L m hm p q h n f j = translation K m hm p q h (g) (c) := by
  rw [extendedTranslation, ← PolygonActionFieldExtension.action,
    ← comp_whiskerRight_assoc, extendedParameter_group]
  rfl

/-- The intrinsic field-coordinate translation is the hom of the original full isomorphism. -/
theorem extendedTranslation_iso_hom :
    (translationIso K m hm p q h (g) (c)).hom =
      extendedTranslation K L m hm p q h n f j := by
  rw [translationIso_hom, extendedTranslation_eq]

/-- Common relabeling preserves the original section in extension-field coordinates. -/
theorem extendedParameter_action (r : RelabelGroup n) :
    extendedParameter K L m n (f ≫ (action (G K m) n r).hom) j =
      extendedParameter K L m n f (r.2.2.symm j) := by
  unfold extendedParameter
  rw [section_action_cyclic]

/-- The same finite action retains the actual intrinsic whole-polygon translations. -/
theorem extendedTranslation_action (r : RelabelGroup n) :
    extendedTranslation K L m hm p q h n (f ≫ (action (G K m) n r).hom) j =
      extendedTranslation K L m hm p q h n f (r.2.2.symm j) := by
  unfold extendedTranslation
  rw [extendedParameter_action]

end FLT.Mazur.PolygonCyclicBoundary
