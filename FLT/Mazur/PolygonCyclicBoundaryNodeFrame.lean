/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryDivisor
public import FLT.Mazur.PolygonParameterNormalizationLine

/-!
# Exact node frames on the actual cyclic boundary parameters

Each translated original node carries the canonical empty-divisor frame for
its corresponding translated marking. Common relabeling retains both the
whole node map and that frame, including its exact unit-section equation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open CyclicBoundaryParameter CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso
  PolygonMarkingBaseChange.markingIdeal movedMarkingIdeal
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n] {T : Scheme} (g : T ⟶ Spec (.of K))
  (f : Over.mk g ⟶ parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "c" => markedSection (G K m) n g f (1, 1, j)

/-- The original node translated by the actual cyclic parameter section. -/
def labelNode : ((Over.pullback g).obj (point K)).left ⟶ ((Over.pullback g).obj C).left :=
  ((Over.pullback g).map (nodeι K m k ≫ q)).left ≫
    (translationIso K m hm p q h g (c)).hom.left

/-- The canonical frame of the translated marking line at the translated original node. -/
def labelNodeFrame :
    (Scheme.Modules.pullback (labelNode K m hm p q h n g f j k)).obj
      (divisorLineBundle (labelIdeal K m hm p q h n g f a i j)
        (labelIdeal_cartier K m hm p q h n g f a i j).1) ≅
          divisorLineBundle ⊤ effectiveCartier_top :=
  movedNodeLineIso K m hm p q h g (c) a i k

/-- The actual frame carries the canonical marking section to the unit, with no scalar. -/
@[reassoc] theorem labelNodeFrame_unit :
    (Scheme.Modules.pullback (labelNode K m hm p q h n g f j k)).map
        (divisorSectionMap (labelIdeal_cartier K m hm p q h n g f a i j).1) ≫
      (labelNodeFrame K m hm p q h n g f a i j k).hom ≫
        (divisorLineBundleTopIso effectiveCartier_top).hom =
          (modulePullbackUnitIso (labelNode K m hm p q h n g f j k)).hom := by
  have hs : DivisorLineSectionCompatible (labelNode K m hm p q h n g f j k)
      (labelIdeal_cartier K m hm p q h n g f a i j).1 effectiveCartier_top
      (labelNodeFrame K m hm p q h n g f a i j k) :=
    movedNodeLineIso_section K m hm p q h g (c) a i k
  rw [← Category.assoc, hs.section, Category.assoc, divisorSection_top_map,
    Iso.inv_hom_id, Category.comp_id]

/-- The common finite action retains the actual translated node under the prescribed labels. -/
theorem labelNode_action (e : RelabelGroup n) :
    labelNode K m hm p q h n g (f ≫ (action (G K m) n e).hom) j k =
      labelNode K m hm p q h n g f (e.2.2.symm j) k := by
  unfold labelNode
  rw [section_action_cyclic]

/-- Relabeling retains the original frame itself, after its exact label identifications. -/
theorem labelNodeFrame_action (e : RelabelGroup n) :
    HEq (labelNodeFrame K m hm p q h n g (f ≫ (action (G K m) n e).hom) a i j k)
      (labelNodeFrame K m hm p q h n g f a i (e.2.2.symm j) k) := by
  have he (u v : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K m)) (huv : u = v) :
      HEq (movedNodeLineIso K m hm p q h g u a i k)
        (movedNodeLineIso K m hm p q h g v a i k) := by
    cases huv
    rfl
  exact he _ _ (section_action_cyclic (G K m) n g f e j)

end FLT.Mazur.PolygonCyclicBoundary
