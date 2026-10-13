/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductLine
public import FLT.Mazur.DivisorLineSectionIdealTransport
public import FLT.Mazur.DivisorLineSectionIdentity

/-!
# Identity normalization of the full varying product marking

Translation by the identity section recovers the actual original product.
After that ideal identification, its section-preserving positive-line
comparison is exactly the pullback unitor on the whole polygon family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : Fin n → Kˣ)

/-- The identity section acts by the actual identity of the whole base-changed polygon. -/
theorem translationIso_one_hom_left :
    (translationIso K n hn p q h g 1).hom.left = 𝟙 ((Over.pullback g).obj C).left := by
  have he := translation_one K n hn p q h g
  rw [← translationIso_hom] at he
  exact congrArg Over.Hom.left he

/-- At the identity section the moved full product is the original ideal itself. -/
theorem movedProductMarkingIdeal_one :
    movedProductMarkingIdeal K n hn p q h g 1 a = productMarkingIdeal K n p g a := by
  have he := movedProductMarkingIdeal_pullback K n hn p q h g 1 a
  rwa [translationIso_one_hom_left, Scheme.IdealSheafData.comap_id] at he

/-- The identity comparison after identifying the full original product ideal. -/
irreducible_def unitProductMarkingLineIso :
    (Scheme.Modules.pullback (translationIso K n hn p q h g 1).hom.left).obj
      (productMarkingLine K n hn p q h g a) ≅ productMarkingLine K n hn p q h g a :=
  (Scheme.Modules.pullback _).mapIso
    (divisorLineBundleEqIso (movedProductMarkingIdeal_one K n hn p q h g a).symm
      (productMarkingIdeal_cartier K n hn p q h g a).1
      (movedProductMarkingIdeal_cartier K n hn p q h g 1 a).1) ≪≫
    movedProductMarkingLineIso K n hn p q h g 1 a

/-- The normalized identity comparison retains the whole product's canonical section. -/
theorem unitProductMarkingLineIso_section :
    DivisorLineSectionCompatible (translationIso K n hn p q h g 1).hom.left
      (productMarkingIdeal_cartier K n hn p q h g a).1
      (productMarkingIdeal_cartier K n hn p q h g a).1
      (unitProductMarkingLineIso K n hn p q h g a) := by
  rw [unitProductMarkingLineIso_def]
  exact (movedProductMarkingLineIso_section K n hn p q h g 1 a).sourceIdealEq
    (movedProductMarkingIdeal_one K n hn p q h g a).symm

/-- The normalized full-product identity comparison is precisely the pullback unitor. -/
theorem unitProductMarkingLineIso_eq :
    unitProductMarkingLineIso K n hn p q h g a =
      (Scheme.Modules.pullbackCongr (translationIso_one_hom_left K n hn p q h g)).app _ ≪≫
        (Scheme.Modules.pullbackId _).app (productMarkingLine K n hn p q h g a) :=
  (unitProductMarkingLineIso_section K n hn p q h g a).eq_id
    (translationIso_one_hom_left K n hn p q h g)

end FLT.Mazur.PolygonParameterTranslation
