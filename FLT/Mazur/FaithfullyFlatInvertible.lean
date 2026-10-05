/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FaithfullyFlatFinitePresentation
public import Mathlib.RingTheory.PicardGroup

/-!
# Faithfully flat descent of invertible modules

Finite presentation descends. Flat base change then commutes with the dual,
and faithful flatness reflects bijectivity of the dual evaluation map.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Duals of finitely presented modules commute with flat scalar extension. -/
def flatDualBaseChange [Module.Flat R S] [Module.FinitePresentation R M] :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (Module.FinitePresentation.isBaseChange_map R M R S).equiv ≪≫ₗ
    LinearEquiv.congrRight (AlgebraTensorModule.rid R S S)

/-- The dual comparison evaluates by extending the original functional. -/
@[simp]
theorem flatDualBaseChange_tmul [Module.Flat R S] [Module.FinitePresentation R M]
    (s t : S) (f : Module.Dual R M) (m : M) :
    flatDualBaseChange (s ⊗ₜ[R] f) (t ⊗ₜ[R] m) = (s * t) * algebraMap R S (f m) := by
  simp [flatDualBaseChange, IsBaseChange.equiv_tmul, Algebra.smul_def, mul_assoc, mul_comm]

/-- Scalar extension identifies the evaluation source with evaluation after extension. -/
def flatEvaluationSource [Module.Flat R S] [Module.FinitePresentation R M] :
    S ⊗[R] (Module.Dual R M ⊗[R] M) ≃ₗ[S]
      Module.Dual S (S ⊗[R] M) ⊗[S] (S ⊗[R] M) :=
  AlgebraTensorModule.distribBaseChange R S (Module.Dual R M) M ≪≫ₗ
    TensorProduct.congr flatDualBaseChange (LinearEquiv.refl S _)

/-- Dual evaluation commutes with flat base change. -/
theorem flatEvaluation_comm [Module.Flat R S] [Module.FinitePresentation R M] :
    (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
        (contractLeft R M).baseChange S =
      contractLeft S (S ⊗[R] M) ∘ₗ (flatEvaluationSource (R := R) (S := S) (M := M)) := by
  ext s f
  simp [flatEvaluationSource, AlgebraTensorModule.distribBaseChange, flatDualBaseChange_tmul,
    Algebra.smul_def]

/-- Invertibility reflects across faithfully flat scalar extension. -/
theorem invertible_of_faithfullyFlat [Module.FaithfullyFlat R S]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  have : Module.FinitePresentation S (S ⊗[R] M) :=
    Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation R M :=
    FCurve.finitePresentation_of_faithfullyFlat (S := S)
  constructor
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S _).mp
  have h := (Module.Invertible.bijective (R := S) (M := S ⊗[R] M)).comp
    (flatEvaluationSource (R := R) (S := S) (M := M)).bijective
  change Function.Bijective (contractLeft S (S ⊗[R] M) ∘ₗ
    (flatEvaluationSource (R := R) (S := S) (M := M)).toLinearMap) at h
  rw [← flatEvaluation_comm] at h
  constructor
  · intro x y hxy
    apply h.1
    exact congrArg (AlgebraTensorModule.rid R S S) hxy
  · intro y
    obtain ⟨x, hx⟩ := h.2 ((AlgebraTensorModule.rid R S S) y)
    exact ⟨x, (AlgebraTensorModule.rid R S S).injective hx⟩

/-- Faithfully flat scalar extension detects invertibility exactly. -/
theorem invertible_faithfullyFlat_iff [Module.FaithfullyFlat R S] :
    Module.Invertible S (S ⊗[R] M) ↔ Module.Invertible R M :=
  ⟨fun _ ↦ invertible_of_faithfullyFlat (S := S), fun _ ↦ inferInstance⟩

end FLT.Mazur
