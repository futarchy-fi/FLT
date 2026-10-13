/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductMarking

/-!
# Positive lines of full polygon product markings

Both parameter change and varying translation preserve the canonical section
of the entire boundary divisor. The comparisons use the actual ideal sheaves.
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
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Fin n → Kˣ)

/-- The positive line of the original boundary product over the parameter scheme. -/
def productMarkingLine : ((Over.pullback g).obj C).left.Modules :=
  divisorLineBundle (productMarkingIdeal K n p g a)
    (productMarkingIdeal_cartier K n hn p q h g a).1

/-- The positive line of the full translated product. -/
def movedProductMarkingLine : ((Over.pullback g).obj C).left.Modules :=
  divisorLineBundle (movedProductMarkingIdeal K n hn p q h g c a)
    (movedProductMarkingIdeal_cartier K n hn p q h g c a).1

/-- The product-line comparison for the actual varying translation. -/
irreducible_def movedProductMarkingLineIso :
    (Scheme.Modules.pullback (translationIso K n hn p q h g c).hom.left).obj
      (movedProductMarkingLine K n hn p q h g c a) ≅
        productMarkingLine K n hn p q h g a := by
  let hs := (movedProductMarkingIdeal_cartier K n hn p q h g c a).1
  let ht := (productMarkingIdeal_cartier K n hn p q h g a).1
  let he := movedProductMarkingIdeal_pullback K n hn p q h g c a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The entire moved product retains its original canonical vanishing section. -/
theorem movedProductMarkingLineIso_section :
    DivisorLineSectionCompatible (translationIso K n hn p q h g c).hom.left
      (movedProductMarkingIdeal_cartier K n hn p q h g c a).1
      (productMarkingIdeal_cartier K n hn p q h g a).1
      (movedProductMarkingLineIso K n hn p q h g c a) := by
  let hs := (movedProductMarkingIdeal_cartier K n hn p q h g c a).1
  let ht := (productMarkingIdeal_cartier K n hn p q h g a).1
  let he := movedProductMarkingIdeal_pullback K n hn p q h g c a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [movedProductMarkingLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The actual product line is the pullback of the original boundary divisor line. -/
irreducible_def productMarkingLineIso :
    (Scheme.Modules.pullback (pullback.fst C.hom g)).obj
      (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a)
        (PolygonBoundaryDivisor.cartier K n p hn q h a).1) ≅
          productMarkingLine K n hn p q h g a := by
  let hs := (PolygonBoundaryDivisor.cartier K n p hn q h a).1
  let ht := (productMarkingIdeal_cartier K n hn p q h g a).1
  let he := (productMarkingIdeal_original K n p g a).symm
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- Parameter change preserves the section of the whole original product. -/
theorem productMarkingLineIso_section :
    DivisorLineSectionCompatible (pullback.fst C.hom g)
      (PolygonBoundaryDivisor.cartier K n p hn q h a).1
      (productMarkingIdeal_cartier K n hn p q h g a).1
      (productMarkingLineIso K n hn p q h g a) := by
  let hs := (PolygonBoundaryDivisor.cartier K n p hn q h a).1
  let ht := (productMarkingIdeal_cartier K n hn p q h g a).1
  let he := (productMarkingIdeal_original K n p g a).symm
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [productMarkingLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonParameterTranslation
