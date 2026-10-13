/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterMarkingLine
public import FLT.Mazur.PolygonNormalizationNodeBaseChange

/-!
# Original normalization and node lines under varying polygon translations

Compose the original normalization and node maps with the whole-polygon
translation. The moved marking line recovers the original component lines and
node frame, with the original endpoint incidence triangle unchanged.
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
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Kˣ) (j i : Fin n)
local notation "F" => Over.pullback g
local notation "τ" => Over.Hom.left (Iso.hom (translationIso K n hn p q h g c))

/-- The actual moved marking line on each translated original normalization component. -/
def movedNormalizationLineIso :
    (Scheme.Modules.pullback (((F).map (componentι K n i ≫ p)).left ≫ τ)).obj
      (movedMarkingLine K n hn p q h g c a j) ≅
        normalizationMarkingLine K n hn p q h a j i g :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (movedMarkingLineIso K n hn p q h g c a j) ≪≫
      normalizationLineIso K n hn p q h a j i g

/-- The translated original component comparison retains its canonical marking section. -/
theorem movedNormalizationLineIso_section :
    DivisorLineSectionCompatible (((F).map (componentι K n i ≫ p)).left ≫ τ)
      (movedMarkingIdeal_cartier K n hn p q h g c a j).1
      (relativeCartierBaseChange (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q h a j i)).1
      (movedNormalizationLineIso K n hn p q h g c a j i) :=
  (movedMarkingLineIso_section K n hn p q h g c a j).comp
    (normalizationLineIso_section K n hn p q h a j i g)

/-- The translated original node retains the original empty-divisor line frame. -/
def movedNodeLineIso :
    (Scheme.Modules.pullback (((F).map (nodeι K n i ≫ q)).left ≫ τ)).obj
      (movedMarkingLine K n hn p q h g c a j) ≅
        divisorLineBundle ⊤ effectiveCartier_top :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (movedMarkingLineIso K n hn p q h g c a j) ≪≫
      nodeLineIso K n hn p q h g a j i

/-- The node comparison preserves the canonical unit section of the node frame. -/
theorem movedNodeLineIso_section :
    DivisorLineSectionCompatible (((F).map (nodeι K n i ≫ q)).left ≫ τ)
      (movedMarkingIdeal_cartier K n hn p q h g c a j).1 effectiveCartier_top
      (movedNodeLineIso K n hn p q h g c a j i) :=
  (movedMarkingLineIso_section K n hn p q h g c a j).comp
    (nodeLineIso_section K n hn p q h g a j i)

variable (k : Fin n) (s : point K ⟶ component K)
  (w : s ≫ (componentι K n i ≫ p) = nodeι K n k ≫ q)

/-- Either original branch still recovers the same translated node and its exact line frame. -/
theorem movedNormalizationLineIso_node :
    LinePullbackTriangle ((F).map s).left
      (((F).map (componentι K n i ≫ p)).left ≫ τ)
      (((F).map (nodeι K n k ≫ q)).left ≫ τ)
      (by rw [← Category.assoc, normalizationNode_baseChange_left K n p q g i k s w])
      (movedNormalizationLineIso K n hn p q h g c a j i)
      (normalizationEndpointLineIso K n hn p q h g a j i k s w)
      (movedNodeLineIso K n hn p q h g c a j k) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (movedNormalizationLineIso_section K n hn p q h g c a j i)
    (normalizationEndpointLineIso_section K n hn p q h g a j i k s w)
    (movedNodeLineIso_section K n hn p q h g c a j k)

end FLT.Mazur.PolygonParameterTranslation
