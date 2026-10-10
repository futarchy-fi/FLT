/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntegerModel
public import FLT.Mazur.CoefficientModelRecovery
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Smooth affine models at a common coefficient stage

Finitely many smooth affine algebras have smooth affine scheme models over
one finite integer coefficient ring. The stage can extend a prescribed model
ring and retain prescribed coefficients; recovery is genuinely cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A smooth affine algebra has a smooth affine scheme model over finite coefficients. -/
theorem exists_smooth_affine_coefficient_model {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)), IsAffine Y ∧ Smooth q ∧
        ∃ f : Spec (.of B) ⟶ Y,
          IsPullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) q
            (Spec.map (CommRingCat.ofHom S.val.toRingHom)) := by
  obtain ⟨S, C, _, _, hS, hC, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg (R := ℤ)
    (A := A) (B := B)
  refine ⟨S, S.fg_iff_finiteType.mp hS, Spec (.of C),
    Spec.map (CommRingCat.ofHom (algebraMap S C)), inferInstance, ?_,
    _, integerModel_isPullback e.symm⟩
  apply HasRingHomProperty.Spec_iff.mpr
  exact (RingHom.smooth_algebraMap).mpr hC

/-- A finite smooth affine family descends to one enlargement of any initial coefficient ring. -/
theorem exists_common_smooth_affine_coefficient_models {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {ι : Type v} [Finite ι] (B : ι → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra.Smooth A (B i)]
    (c : Set A) (hc : c.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ c ⊆ S ∧ S₀ ≤ S ∧
      ∀ j, ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)), IsAffine Y ∧ Smooth q ∧
        ∃ f : Spec (.of (B j)) ⟶ Y,
          IsPullback f (Spec.map (CommRingCat.ofHom (algebraMap A (B j)))) q
            (Spec.map (CommRingCat.ofHom S.val.toRingHom)) := by
  choose R hR Y q hY hq f hf using
    fun j ↦ exists_smooth_affine_coefficient_model (A := A) (B := B j)
  obtain ⟨S, hS, hcS, h₀S, hRS⟩ := exists_common_coefficient_extension S₀ R hR c hc
  refine ⟨S, hS, hcS, h₀S, fun j ↦ ?_⟩
  let i : (CoefficientStage (R j))ᵒᵖ := .op ⟨S, hRS j, hS⟩
  refine ⟨(coefficientModelDiagram (R j) (q j)).obj i,
    pullback.snd (q j) ((coefficientSpectrumToInitial (R j)).app i),
    ?_, inferInstance, coefficientModelRecovery (hf j) i,
    coefficientModelRecovery_isPullback (hf j) i⟩
  let _ := hY j
  let _ : IsAffine ((coefficientSpectrumDiagram (R j)).obj i) :=
    inferInstanceAs (IsAffine (Spec (.of S)))
  change IsAffine (pullback (q j) ((coefficientSpectrumToInitial (R j)).app i))
  infer_instance

end FLT.Mazur.Approximation
