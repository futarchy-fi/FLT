/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductNormalization
public import FLT.Mazur.PolygonParameterProductBaseChange
public import FLT.Mazur.PolygonParameterNormalizationRefinement

/-!
# Refinement square of the full translated normalization line

The original normalization marking, the full translated product and the actual
composition charts give a commuting square of positive lines. Both routes
preserve their canonical sections over arbitrary further parameter schemes.
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
local notation "J" => Scheme.IdealSheafData.comap
  (Scheme.Hom.ker (PolygonMarkedSections.sectionMap K n p (a i) i))
  (Over.Hom.left (componentι K n i ≫ p))
local notation "hJ" => normalizationIdeal_relativeCartier K n hn p q h (a i) i i
local notation "ν" => CategoryTheory.Functor.map (Over.pullback g) (componentι K n i ≫ p) ≫
  Iso.hom (translationIso K n hn p q h g c)
local notation "ν'" => CategoryTheory.Functor.map (Over.pullback (k ≫ g)) (componentι K n i ≫ p) ≫
  Iso.hom (translationIso K n hn p q h (k ≫ g) (parameterBaseChange K n g k c))
local notation "δC" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g))
  (C))
local notation "δP" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g))
  (component K))

/-- The translated full product restricts to the original component ideal itself. -/
theorem movedProductMarkingIdeal_normalization :
    (movedProductMarkingIdeal K n hn p q h g c a).comap (ν).left =
      (J).comap (pullback.fst (component K).hom g) := by
  rw [Over.comp_left, Scheme.IdealSheafData.comap_comp,
    movedProductMarkingIdeal_pullback, productMarkingIdeal_normalization K n hn p q h]

/-- The normalization comparison on the actual iterated family. -/
irreducible_def movedProductNormalizationIteratedIso :
    (Scheme.Modules.pullback ((Over.pullback k).map (ν)).left).obj
      (divisorLineBundle ((movedProductMarkingIdeal K n hn p q h g c a).comap
        (pullback.fst ((Over.pullback g).obj C).hom k))
        (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
          (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1) ≅
      divisorLineBundle (((J).comap (pullback.fst (component K).hom g)).comap
        (pullback.fst ((Over.pullback g).obj (component K)).hom k))
        (relativeCartierBaseChange ((Over.pullback g).obj (component K)).hom k _
          (relativeCartierBaseChange (component K).hom g _ (hJ))).1 :=
  relativeCartierMorphismBaseChangeIso (ν) k _ _
    (movedProductMarkingIdeal_cartier K n hn p q h g c a)
    (relativeCartierBaseChange (component K).hom g _ (hJ))
    (movedProductMarkingIdeal_normalization K n hn p q h g c a i)

/-- The iterated normalization comparison retains its canonical section. -/
theorem movedProductNormalizationIteratedIso_section :
    DivisorLineSectionCompatible ((Over.pullback k).map (ν)).left
      (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
        (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1
      (relativeCartierBaseChange ((Over.pullback g).obj (component K)).hom k _
        (relativeCartierBaseChange (component K).hom g _ (hJ))).1
      (movedProductNormalizationIteratedIso K n hn p q h g k c a i) := by
  rw [movedProductNormalizationIteratedIso_def]
  exact relativeCartierMorphismBaseChangeIso_section _ _ _ _ _ _ _

/-- Refinement of the original translated normalization commutes on the full product line. -/
theorem movedProductNormalization_refinement_square :
    LinePullbackSquare ((Over.pullback k).map (ν)).left (δC) (δP) (ν').left
      (congrArg Over.Hom.left (translatedNormalization_baseChange K n hn p q h g k c i))
      (movedProductMarkingBaseChangeLineIso K n hn p q h g k c a)
      (movedProductNormalizationIteratedIso K n hn p q h g k c a i)
      (movedProductNormalizationLineIso K n hn p q h (k ≫ g)
        (parameterBaseChange K n g k c) a i)
      (relativeCartierBaseChangeCompositionIso (component K) g k (J) (hJ)) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (movedProductMarkingBaseChangeLineIso_section K n hn p q h g k c a)
    (movedProductNormalizationIteratedIso_section K n hn p q h g k c a i)
    (movedProductNormalizationLineIso_section K n hn p q h (k ≫ g)
      (parameterBaseChange K n g k c) a i)
    (relativeCartierBaseChangeCompositionIso_section (component K) g k (J) (hJ))

end FLT.Mazur.PolygonParameterTranslation
