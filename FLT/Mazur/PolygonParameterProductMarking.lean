/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterMarkingLine
public import FLT.Mazur.PolygonBoundaryDivisor

/-!
# Full product markings under varying polygon translations

The product retains every original marked Cartier ideal. Arbitrary group
sections transport this entire divisor, including over nonreduced bases.
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

/-- The entire original boundary product after arbitrary parameter change. -/
def productMarkingIdeal : ((Over.pullback g).obj C).left.IdealSheafData :=
  ∏ i, markingIdeal K n p g (a i) i

omit [NeZero n] in
/-- The product is the pullback of the original boundary divisor itself. -/
theorem productMarkingIdeal_original :
    productMarkingIdeal K n p g a =
      (PolygonBoundaryDivisor.ideal K n p a).comap (pullback.fst C.hom g) := by
  rw [productMarkingIdeal, PolygonBoundaryDivisor.ideal, idealSheaf_comap_prod]
  simp only [markingIdeal]

include h in
/-- The original product remains relative Cartier over every parameter scheme. -/
theorem productMarkingIdeal_cartier :
    RelativeEffectiveCartier ((Over.pullback g).obj C).hom
      (productMarkingIdeal K n p g a) :=
  relativeEffectiveCartier_prod _ Finset.univ _ fun i _ ↦
    markingIdeal_cartier K n hn p q h g (a i) i

/-- The product of all translated original marking ideals. -/
def movedProductMarkingIdeal : ((Over.pullback g).obj C).left.IdealSheafData :=
  ∏ i, movedMarkingIdeal K n hn p q h g c (a i) i

/-- Translation of the whole product agrees with translation of its actual factors. -/
theorem movedProductMarkingIdeal_eq :
    movedProductMarkingIdeal K n hn p q h g c a =
      (productMarkingIdeal K n p g a).comap
        (translationIso K n hn p q h g c).inv.left := by
  rw [movedProductMarkingIdeal, productMarkingIdeal, idealSheaf_comap_prod]
  simp only [movedMarkingIdeal]

/-- The full moved product is relative Cartier, with no restriction on the section. -/
theorem movedProductMarkingIdeal_cartier :
    RelativeEffectiveCartier ((Over.pullback g).obj C).hom
      (movedProductMarkingIdeal K n hn p q h g c a) :=
  relativeEffectiveCartier_prod _ Finset.univ _ fun i _ ↦
    movedMarkingIdeal_cartier K n hn p q h g c (a i) i

/-- Pulling back the entire translated product recovers every original factor. -/
theorem movedProductMarkingIdeal_pullback :
    (movedProductMarkingIdeal K n hn p q h g c a).comap
      (translationIso K n hn p q h g c).hom.left = productMarkingIdeal K n p g a := by
  simp only [movedProductMarkingIdeal, idealSheaf_comap_prod,
    movedMarkingIdeal_pullback, productMarkingIdeal]

end FLT.Mazur.PolygonParameterTranslation
