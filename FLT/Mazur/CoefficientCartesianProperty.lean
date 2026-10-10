/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientRecoveredProperty
public import FLT.Mazur.CoefficientModelRecovery

/-!
# Cartesian models and iterated coefficient enlargement

Two cartesian models of the same family can be compared without choosing a
map at a finite stage. Stable properties also pass from an iterated model
to the corresponding single enlargement of the original model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Cartesian models of one family share stable properties at a finite stage. -/
theorem exists_coefficient_property_of_cartesian_models {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {X Y Z : Scheme.{u}} (r : X ⟶ Spec (.of A))
    (p : Y ⟶ Spec (.of S₀)) (q : Z ⟶ Spec (.of S₀))
    [QuasiCompact p] [QuasiCompact q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    {a : X ⟶ Y} {b : X ⟶ Z}
    (hp : IsPullback a r p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
    (hq : IsPullback b r q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
    (W : MorphismProperty Scheme.{u}) [W.IsStableUnderBaseChange] [W.RespectsIso]
    (hW : W q) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      W (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  let F := hp.isoPullback.inv ≫ hq.isoPullback.hom
  have hF : F ≫ pullback.snd q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) =
      pullback.snd p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) := by
    simp only [F, Category.assoc, hq.isoPullback_hom_snd, hp.isoPullback_inv_snd]
  exact exists_coefficient_property_of_recovered_iso S₀ p q F hF W hW

/-- A property obtained after restarting the coefficient system holds at a single stage. -/
theorem coefficient_property_of_iterated_enlargement {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of S₀))
    (i : (CoefficientStage S₀)ᵒᵖ) (j : (CoefficientStage i.unop.val)ᵒᵖ)
    (W : MorphismProperty Scheme.{u}) [W.RespectsIso]
    (hW : W (pullback.snd
      (pullback.snd p ((coefficientSpectrumToInitial S₀).app i))
      ((coefficientSpectrumToInitial i.unop.val).app j))) :
    W (pullback.snd p ((coefficientSpectrumToInitial S₀).app
      (.op ⟨j.unop.val, i.unop.property.1.trans j.unop.property.1,
        j.unop.property.2⟩))) := by
  have hb : (coefficientSpectrumToInitial i.unop.val).app j ≫
      (coefficientSpectrumToInitial S₀).app i =
      (coefficientSpectrumToInitial S₀).app
        (.op ⟨j.unop.val, i.unop.property.1.trans j.unop.property.1,
          j.unop.property.2⟩) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hc := (IsPullback.of_hasPullback
    (pullback.snd p ((coefficientSpectrumToInitial S₀).app i))
    ((coefficientSpectrumToInitial i.unop.val).app j)).paste_horiz
      (IsPullback.of_hasPullback p ((coefficientSpectrumToInitial S₀).app i))
  rw [hb] at hc
  rwa [← W.cancel_left_of_respectsIso hc.isoPullback.hom, hc.isoPullback_hom_snd]

end FLT.Mazur.Approximation
