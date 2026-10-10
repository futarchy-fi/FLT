/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoefficientSmoothDescent
public import FLT.Mazur.FiniteCoefficientProperties

/-!
# Smoothness descends for finitely presented coefficient models

Choose a finite affine cover of the fixed model. Each chart becomes smooth
at a finite stage; one common enlargement retains the actual base-changed
cover. Source locality then proves smoothness of the whole fixed model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Smoothness of the recovered model descends, retaining prescribed coefficients. -/
theorem exists_coefficient_smooth {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of S₀))
    [QuasiCompact p] [LocallyOfFinitePresentation p]
    [Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))]
    (c : Set A) (hc : c.Finite) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ, c ⊆ i.unop.val ∧
      Smooth (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let U := Y.affineCover.finiteSubcover
  let b := Spec.map (CommRingCat.ofHom S₀.val.toRingHom)
  have hcharts (t : U.I₀) : ∃ i : (CoefficientStage S₀)ᵒᵖ,
      Smooth (pullback.snd (U.f t ≫ p) ((coefficientSpectrumToInitial S₀).app i)) := by
    let V := Scheme.Pullback.openCoverOfLeft U p b
    have hcomp : V.f t ≫ pullback.snd p b = pullback.snd (U.f t ≫ p) b := by
      simp [V, Scheme.Pullback.openCoverOfLeft]
    have : Smooth (pullback.snd (U.f t ≫ p) b) := by
      rw [← hcomp]
      infer_instance
    exact exists_coefficient_smooth_of_affine_recovery S₀
      (pullback.snd (U.f t ≫ p) b) (U.f t ≫ p)
      (IsPullback.of_hasPullback (U.f t ≫ p) b)
  obtain ⟨i, hci, hi⟩ := exists_common_coefficient_properties S₀
    (fun t ↦ U.f t ≫ p) (fun _ ↦ @Smooth) hcharts c hc
  refine ⟨i, hci, ?_⟩
  let V := Scheme.Pullback.openCoverOfLeft U p ((coefficientSpectrumToInitial S₀).app i)
  apply IsZariskiLocalAtSource.of_openCover V
  intro t
  simpa [V, Scheme.Pullback.openCoverOfLeft] using hi t

/-- Any cartesian recovery of a smooth family gives smoothness at a finite stage. -/
theorem exists_coefficient_smooth_of_cartesian {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {X Y : Scheme.{u}} (r : X ⟶ Spec (.of A)) [Smooth r]
    (p : Y ⟶ Spec (.of S₀)) [QuasiCompact p] [LocallyOfFinitePresentation p]
    {a : X ⟶ Y}
    (hp : IsPullback a r p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
    (c : Set A) (hc : c.Finite) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ, c ⊆ i.unop.val ∧
      Smooth (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  have : Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Smooth hp.isoPullback.hom,
      hp.isoPullback_hom_snd]
    infer_instance
  exact exists_coefficient_smooth S₀ p c hc

end FLT.Mazur.Approximation
