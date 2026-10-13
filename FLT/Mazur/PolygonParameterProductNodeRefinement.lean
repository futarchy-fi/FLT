/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductNode
public import FLT.Mazur.PolygonParameterProductBaseChange
public import FLT.Mazur.PolygonParameterNormalizationRefinement

/-!
# Refinement square of the full translated node frame

The canonical empty-divisor frame of the original translated node commutes
with arbitrary parameter refinement and the actual pullback composition chart.
Both routes preserve the canonical unit section exactly.
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
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Fin n → Kˣ) (i : Fin n)
local notation "ν" => CategoryTheory.Functor.map (Over.pullback g) (nodeι K n i ≫ q) ≫
  Iso.hom (translationIso K n hn p q h g c)
local notation "ν'" => CategoryTheory.Functor.map (Over.pullback (k ≫ g)) (nodeι K n i ≫ q) ≫
  Iso.hom (translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c))
local notation "δC" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g))
  (C))
local notation "δP" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g))
  (point K))

/-- The full translated product is still the unit ideal on the translated original node. -/
theorem movedProductMarkingIdeal_node :
    (movedProductMarkingIdeal K n hn p q h g c a).comap (ν).left = ⊤ := by
  rw [Over.comp_left, Scheme.IdealSheafData.comap_comp,
    movedProductMarkingIdeal_pullback, productMarkingIdeal_node K n hn p q h]

/-- Further base change preserves the unit ideal at the entire original translated node. -/
theorem movedProductMarkingIdeal_iterated_node :
    ((movedProductMarkingIdeal K n hn p q h g c a).comap
      (pullback.fst ((Over.pullback g).obj C).hom k)).comap
        ((Over.pullback k).map (ν)).left = ⊤ := by
  have he := relativeCartierMorphismBaseChange_ideal (ν) k _ _
    (movedProductMarkingIdeal_node K n hn p q h g c a i)
  exact he.trans (Scheme.IdealSheafData.comap_top _)

/-- The node comparison on the actual iterated family has the original unit frame. -/
irreducible_def movedProductNodeIteratedIso :
    (Scheme.Modules.pullback ((Over.pullback k).map (ν)).left).obj
      (divisorLineBundle ((movedProductMarkingIdeal K n hn p q h g c a).comap
        (pullback.fst ((Over.pullback g).obj C).hom k))
        (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
          (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1) ≅
      divisorLineBundle ⊤ effectiveCartier_top := by
  let hs := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1
  let he := movedProductMarkingIdeal_iterated_node K n hn p q h g k c a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq _ hs effectiveCartier_top he

/-- The iterated node comparison preserves the full product's canonical section. -/
theorem movedProductNodeIteratedIso_section :
    DivisorLineSectionCompatible ((Over.pullback k).map (ν)).left
      (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
        (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1 effectiveCartier_top
      (movedProductNodeIteratedIso K n hn p q h g k c a i) := by
  let hs := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1
  let he := movedProductMarkingIdeal_iterated_node K n hn p q h g k c a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  rw [movedProductNodeIteratedIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Refinement of the original translated node retains the exact full-product line frame. -/
theorem movedProductNode_refinement_square :
    LinePullbackSquare ((Over.pullback k).map (ν)).left (δC) (δP) (ν').left
      (congrArg Over.Hom.left (translatedNode_baseChange K n hn p q h g k c i))
      (movedProductMarkingBaseChangeLineIso K n hn p q h g k c a)
      (movedProductNodeIteratedIso K n hn p q h g k c a i)
      (movedProductNodeLineIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c) a i)
      (divisorEmptyLinePullbackIso (δP)) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (movedProductMarkingBaseChangeLineIso_section K n hn p q h g k c a)
    (movedProductNodeIteratedIso_section K n hn p q h g k c a i)
    (movedProductNodeLineIso_section K n hn p q h (k ≫ g)
      (parameterBaseChange K n g k c) a i)
    (divisorEmptyLinePullbackIso_section (δP))

end FLT.Mazur.PolygonParameterTranslation
