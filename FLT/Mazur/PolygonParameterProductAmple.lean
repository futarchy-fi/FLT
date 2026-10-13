/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProductLine
public import FLT.Mazur.PolygonCubicVeryAmple
public import FLT.Mazur.RelativeAmpleBaseChange
public import FLT.Mazur.RelativeAmplePresentationTransport

/-!
# Ampleness of the full translated product marking

The original boundary product has an explicit cubic projective embedding.
Its positive line remains relatively ample after arbitrary parameter change
and translation by any section of the base-changed polygon group.
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

include h in
/-- The original product marking has an ample positive line by its cubic presentation. -/
theorem originalProductMarkingLine_relativeAmple :
    RelativeAmple C.hom (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a)
      (PolygonBoundaryDivisor.cartier K n p hn q h a).1) :=
  RelativeAmple.of_power (by decide : 0 < 3)
    (PolygonCubicSections.divisor_tensorCube_relativeVeryAmple K n hn p q h a)

/-- Arbitrary parameter change retains ampleness of the whole product marking. -/
theorem productMarkingLine_relativeAmple :
    RelativeAmple ((Over.pullback g).obj C).hom
      (productMarkingLine K n hn p q h g a) :=
  ((originalProductMarkingLine_relativeAmple K n hn p q h a).baseChange
    (PolygonBoundaryDivisor.cartier K n p hn q h a).1.divisorLineBundle_locallyFreeRankOne
      g).of_iso (productMarkingLineIso K n hn p q h g a).symm

/-- The translated whole product remains ample over the same arbitrary parameter scheme. -/
theorem movedProductMarkingLine_relativeAmple :
    RelativeAmple ((Over.pullback g).obj C).hom
      (movedProductMarkingLine K n hn p q h g c a) := by
  let e := (Over.forget T).mapIso (translationIso K n hn p q h g c)
  have hr := (productMarkingLine_relativeAmple K n hn p q h g a)
  have hi := movedProductMarkingLineIso K n hn p q h g c a
  have hs : IsPullback e.inv ((Over.pullback g).obj C).hom
      ((Over.pullback g).obj C).hom (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by
      change (translationIso K n hn p q h g c).inv.left ≫ _ = _ ≫ 𝟙 T
      rw [Over.w, Category.comp_id]⟩
  have hp := hr.of_isPullback
    (productMarkingIdeal_cartier K n hn p q h g a).1.divisorLineBundle_locallyFreeRankOne hs
  exact hp.of_iso ((Scheme.Modules.pullback e.inv).mapIso hi.symm ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr e.inv_hom_id).app _ ≪≫
        (Scheme.Modules.pullbackId _).app _).symm

end FLT.Mazur.PolygonParameterTranslation
