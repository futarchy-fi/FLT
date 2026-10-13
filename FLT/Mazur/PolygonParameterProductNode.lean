/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductLine
public import FLT.Mazur.PolygonNodeBaseChangeLine

/-!
# Full product marking at the original polygon nodes

Every factor is a unit at every original node. The full product therefore
has the canonical empty-divisor frame, retained by varying translations.
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
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Fin n → Kˣ) (i : Fin n)

include h in
/-- The entire boundary product is the unit ideal at every original family node. -/
theorem productMarkingIdeal_node :
    (productMarkingIdeal K n p g a).comap
      ((Over.pullback g).map (nodeι K n i ≫ q)).left = ⊤ := by
  simp only [productMarkingIdeal, idealSheaf_comap_prod, node_ideal K n hn p q h]
  change ∏ _ : Fin n, (1 : ((Over.pullback g).obj (point K)).left.IdealSheafData) = 1
  exact Finset.prod_const_one

/-- The whole product line has the canonical empty-divisor frame at every original node. -/
irreducible_def productNodeLineIso :
    (Scheme.Modules.pullback ((Over.pullback g).map (nodeι K n i ≫ q)).left).obj
      (productMarkingLine K n hn p q h g a) ≅
        divisorLineBundle ⊤ effectiveCartier_top := by
  let hs := (productMarkingIdeal_cartier K n hn p q h g a).1
  let he := productMarkingIdeal_node K n hn p q h g a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq _ hs effectiveCartier_top he

/-- The product node frame preserves the exact canonical section. -/
theorem productNodeLineIso_section :
    DivisorLineSectionCompatible ((Over.pullback g).map (nodeι K n i ≫ q)).left
      (productMarkingIdeal_cartier K n hn p q h g a).1 effectiveCartier_top
      (productNodeLineIso K n hn p q h g a i) := by
  let hs := (productMarkingIdeal_cartier K n hn p q h g a).1
  let he := productMarkingIdeal_node K n hn p q h g a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  rw [productNodeLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The translated original node retains the full product's empty-divisor frame. -/
def movedProductNodeLineIso :
    (Scheme.Modules.pullback (((Over.pullback g).map (nodeι K n i ≫ q)).left ≫
      (translationIso K n hn p q h g c).hom.left)).obj
        (movedProductMarkingLine K n hn p q h g c a) ≅
          divisorLineBundle ⊤ effectiveCartier_top :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (movedProductMarkingLineIso K n hn p q h g c a) ≪≫
      productNodeLineIso K n hn p q h g a i

/-- The moved full product retains the canonical node section without rescaling. -/
theorem movedProductNodeLineIso_section :
    DivisorLineSectionCompatible
      (((Over.pullback g).map (nodeι K n i ≫ q)).left ≫
        (translationIso K n hn p q h g c).hom.left)
      (movedProductMarkingIdeal_cartier K n hn p q h g c a).1 effectiveCartier_top
      (movedProductNodeLineIso K n hn p q h g c a i) :=
  (movedProductMarkingLineIso_section K n hn p q h g c a).comp
    (productNodeLineIso_section K n hn p q h g a i)

/-- The actual translated product section has coordinate one in the original node frame. -/
@[reassoc] theorem movedProductNodeLineIso_unit :
    (Scheme.Modules.pullback (((Over.pullback g).map (nodeι K n i ≫ q)).left ≫
      (translationIso K n hn p q h g c).hom.left)).map
        (divisorSectionMap (movedProductMarkingIdeal_cartier K n hn p q h g c a).1) ≫
      (movedProductNodeLineIso K n hn p q h g c a i).hom ≫
        (divisorLineBundleTopIso effectiveCartier_top).hom =
          (modulePullbackUnitIso _).hom :=
  (movedProductNodeLineIso_section K n hn p q h g c a i).unit _

end FLT.Mazur.PolygonParameterTranslation
