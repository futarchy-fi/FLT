/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianMorphismRecovery
public import FLT.Mazur.CoefficientCartesianHomDescent
public import FLT.Mazur.CoefficientPropertyComparison

/-!
# Properties transferred from an isomorphism after recovery

An isomorphism over the original ring first descends as a map, then becomes
invertible after a second coefficient enlargement. The two enlargements are
combined, so the resulting property concerns the original fixed model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Isomorphic recovered models share stable properties after finite enlargement. -/
theorem exists_coefficient_property_of_recovered_iso {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of S₀)) (q : Z ⟶ Spec (.of S₀))
    [QuasiCompact p] [QuasiCompact q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    (F : (coefficientModelCone S₀ p).pt ⟶ (coefficientModelCone S₀ q).pt)
    [IsIso F]
    (hF : F ≫ pullback.snd q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) =
      pullback.snd p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
    (W : MorphismProperty Scheme.{u}) [W.IsStableUnderBaseChange] [W.RespectsIso]
    (hq : W q) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      W (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  obtain ⟨i, f, hf, hcart⟩ := exists_coefficient_cartesian_hom S₀ p q F hF
  let S := i.unop.val
  let _ : Algebra.FiniteType ℤ S := i.unop.property.2
  let b := (coefficientSpectrumToInitial S₀).app i
  let pi := pullback.snd p b
  let qi := pullback.snd q b
  have : IsIso (immersionBaseChange pi qi f hf
      (Spec.map (CommRingCat.ofHom S.val.toRingHom))) :=
    cartesianMorphismRecovery_isIso (coefficientModelCone_isPullback S₀ p i)
      (coefficientModelCone_isPullback S₀ q i) F f hf hcart.w hF
  have hqi : W qi := W.of_isPullback (IsPullback.of_hasPullback q b) hq
  obtain ⟨j, hj⟩ := exists_coefficient_property_of_comparison S pi qi f hf W hqi
  let k : (CoefficientStage S₀)ᵒᵖ :=
    .op ⟨j.unop.val, i.unop.property.1.trans j.unop.property.1, j.unop.property.2⟩
  have hb : (coefficientSpectrumToInitial S).app j ≫ b =
      (coefficientSpectrumToInitial S₀).app k := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hc := (IsPullback.of_hasPullback pi
    ((coefficientSpectrumToInitial S).app j)).paste_horiz
      (IsPullback.of_hasPullback p b)
  rw [hb] at hc
  refine ⟨k, ?_⟩
  rwa [← W.cancel_left_of_respectsIso hc.isoPullback.hom,
    hc.isoPullback_hom_snd]

end FLT.Mazur.Approximation
