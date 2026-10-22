/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelRecovery
public import FLT.Mazur.SectionCoverBaseChange

/-!+# Retaining the original section under coefficient enlargement

Enlarging a pointed model preserves the actual original section equation.
The section itself has a Cartesian recovery square, so its whole closed
subscheme, including its nonreduced structure, is retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
open SectionCoverBaseChange
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {R : Subalgebra ℤ A}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {p : X ⟶ Spec (.of A)}
  {q : Y ⟶ Spec (.of R)}
  (h : IsPullback f p q (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
  (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
  (t : Spec (.of R) ⟶ Y) (ht : t ≫ q = 𝟙 _)
  (hst : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t = s ≫ f)

include h hs ht hst in
/-- Cartesian recovery of pointed families also recovers the original section square. -/
theorem coefficientSection_isPullback :
    IsPullback s (Spec.map (CommRingCat.ofHom R.val.toRingHom)) f t := by
  apply IsPullback.of_right (h₁₂ := p) (h₂₂ := q)
    (v₁₃ := Spec.map (CommRingCat.ofHom R.val.toRingHom)) _ hst.symm h.flip
  rw [hs, ht]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

include hst hs in
/-- The literal enlarged section recovers the same original marking. -/
theorem coefficientSection_recovery (i : (CoefficientStage R)ᵒᵖ) :
    (coefficientSpectrumCone R).π.app i ≫
      sectionMap q ((coefficientSpectrumToInitial R).app i) t ht =
        s ≫ coefficientModelRecovery h i := by
  apply pullback.hom_ext
  · rw [Category.assoc, sectionMap_fst, ← Category.assoc,
      coefficientSpectrumCone_toInitial, hst, Category.assoc,
      coefficientModelRecovery_fst]
  · simp only [Category.assoc, sectionMap_snd, Category.comp_id,
      coefficientModelRecovery, pullback.lift_snd]
    rw [← Category.assoc, hs]
    exact (Category.id_comp _).symm

include hst hs in
/-- The original closed marking remains Cartesian after every coefficient enlargement. -/
theorem coefficientSection_refined_isPullback (i : (CoefficientStage R)ᵒᵖ) :
    IsPullback s ((coefficientSpectrumCone R).π.app i) (coefficientModelRecovery h i)
      (sectionMap q ((coefficientSpectrumToInitial R).app i) t ht) :=
  coefficientSection_isPullback (coefficientModelRecovery_isPullback h i) s hs _
    (sectionMap_snd q _ t ht) (coefficientSection_recovery h s hs t ht hst i)

end FLT.Mazur.Approximation
