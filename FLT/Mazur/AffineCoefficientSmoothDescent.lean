/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientCartesianProperty
public import FLT.Mazur.SmoothAffineCoefficientModels

/-!
# Smoothness descends on a fixed affine coefficient model

The smooth affine candidate is aligned with the given model by descending
the isomorphism of their recoveries. Thus smoothness is obtained on the
base change of the fixed model, with no finite-stage comparison assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A model recovering a smooth affine algebra becomes smooth after enlargement. -/
theorem exists_coefficient_smooth_of_algebra_model {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of S₀))
    [QuasiCompact p] [LocallyOfFinitePresentation p]
    {a : Spec (.of B) ⟶ Y}
    (hp : IsPullback a (Spec.map (CommRingCat.ofHom (algebraMap A B))) p
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      Smooth (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  obtain ⟨S, hS, _, h₀S, hmodels⟩ := exists_common_smooth_affine_coefficient_models
    S₀ (fun _ : Unit ↦ B) ∅ Set.finite_empty
  obtain ⟨Z, q, hZ, hq, b, hb⟩ := hmodels ()
  let _ := hS
  let _ := hZ
  let _ := hq
  let i : (CoefficientStage S₀)ᵒᵖ := .op ⟨S, h₀S, hS⟩
  let pi := pullback.snd p ((coefficientSpectrumToInitial S₀).app i)
  obtain ⟨j, hj⟩ := exists_coefficient_property_of_cartesian_models S
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) pi q
    (coefficientModelRecovery_isPullback hp i) hb @Smooth hq
  exact ⟨.op ⟨j.unop.val, h₀S.trans j.unop.property.1, j.unop.property.2⟩,
    coefficient_property_of_iterated_enlargement S₀ p i j @Smooth hj⟩

/-- A fixed model with smooth affine recovery becomes smooth at a finite stage. -/
theorem exists_coefficient_smooth_of_affine_recovery {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {X Y : Scheme.{u}} [IsAffine X] (r : X ⟶ Spec (.of A)) [Smooth r]
    (p : Y ⟶ Spec (.of S₀)) [QuasiCompact p] [LocallyOfFinitePresentation p]
    {a : X ⟶ Y}
    (hp : IsPullback a r p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      Smooth (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  let φ := Spec.preimage (X.isoSpec.inv ≫ r)
  let _ : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))) =
      X.isoSpec.inv ≫ r := Spec.map_preimage _
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤)))) := by
    rw [hφ]
    infer_instance
  have : Algebra.Smooth A Γ(X, ⊤) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)
  apply exists_coefficient_smooth_of_algebra_model S₀ p (a := X.isoSpec.inv ≫ a)
  rw [hφ]
  apply hp.of_iso X.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _) <;> simp

end FLT.Mazur.Approximation
