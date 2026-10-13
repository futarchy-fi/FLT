/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductLine
public import FLT.Mazur.PolygonDivisorNormalizationPullback
public import FLT.Mazur.PolygonNormalizationBaseChangeLine

/-!
# Full product marking on the original normalization components

The whole boundary product restricts to exactly its original marked point on
each component. This remains true over arbitrary parameter schemes, and the
positive-line comparisons preserve the canonical sections.
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
/-- The entire product restricts to its own marking on each original family component. -/
theorem productMarkingIdeal_normalization :
    (productMarkingIdeal K n p g a).comap
      ((Over.pullback g).map (componentι K n i ≫ p)).left =
        ((PolygonMarkedSections.sectionMap K n p (a i) i).ker.comap
          (componentι K n i ≫ p).left).comap (pullback.fst (component K).hom g) := by
  rw [productMarkingIdeal_original]
  apply relativeCartierMorphismBaseChange_ideal
  exact (PolygonDivisorNormalizationPullback.ideal K n hn p q h a i).trans
    (PolygonDivisorNormalizationPullback.section_ideal K n hn p q h (a i) i).symm

/-- The original product line restricts to the existing marked-point normalization line. -/
irreducible_def productNormalizationLineIso :
    (Scheme.Modules.pullback ((Over.pullback g).map (componentι K n i ≫ p)).left).obj
      (productMarkingLine K n hn p q h g a) ≅
        normalizationMarkingLine K n hn p q h (a i) i i g := by
  let hs := (productMarkingIdeal_cartier K n hn p q h g a).1
  let ht := (relativeCartierBaseChange (component K).hom g _
    (normalizationIdeal_relativeCartier K n hn p q h (a i) i i)).1
  let he := productMarkingIdeal_normalization K n hn p q h g a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- Restricting the whole product line preserves its exact canonical section. -/
theorem productNormalizationLineIso_section :
    DivisorLineSectionCompatible ((Over.pullback g).map (componentι K n i ≫ p)).left
      (productMarkingIdeal_cartier K n hn p q h g a).1
      (relativeCartierBaseChange (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q h (a i) i i)).1
      (productNormalizationLineIso K n hn p q h g a i) := by
  let hs := (productMarkingIdeal_cartier K n hn p q h g a).1
  let ht := (relativeCartierBaseChange (component K).hom g _
    (normalizationIdeal_relativeCartier K n hn p q h (a i) i i)).1
  let he := productMarkingIdeal_normalization K n hn p q h g a i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [productNormalizationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Varying translation retains the whole product on each translated original component. -/
def movedProductNormalizationLineIso :
    (Scheme.Modules.pullback (((Over.pullback g).map (componentι K n i ≫ p)).left ≫
      (translationIso K n hn p q h g c).hom.left)).obj
        (movedProductMarkingLine K n hn p q h g c a) ≅
          normalizationMarkingLine K n hn p q h (a i) i i g :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (movedProductMarkingLineIso K n hn p q h g c a) ≪≫
      productNormalizationLineIso K n hn p q h g a i

/-- The translated normalization comparison retains the original marked-point section. -/
theorem movedProductNormalizationLineIso_section :
    DivisorLineSectionCompatible
      (((Over.pullback g).map (componentι K n i ≫ p)).left ≫
        (translationIso K n hn p q h g c).hom.left)
      (movedProductMarkingIdeal_cartier K n hn p q h g c a).1
      (relativeCartierBaseChange (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q h (a i) i i)).1
      (movedProductNormalizationLineIso K n hn p q h g c a i) :=
  (movedProductMarkingLineIso_section K n hn p q h g c a).comp
    (productNormalizationLineIso_section K n hn p q h g a i)

end FLT.Mazur.PolygonParameterTranslation
