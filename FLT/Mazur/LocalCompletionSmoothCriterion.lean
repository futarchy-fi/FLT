/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionFaithfullyFlat
public import Mathlib.RingTheory.Smooth.Basic

/-!
# A faithful-completion criterion for formal smoothness

For a Noetherian local algebra essentially of finite type, formal smoothness
is equivalent to flatness of the completed module of differentials and
vanishing of the completed first cotangent homology. These are extensions
of the original algebra's modules, not differentials of the completion.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.LocalCompletionSmoothCriterion

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing A] [IsLocalRing A] [Algebra.EssFiniteType R A]

/-- The actual local completion detects both obstructions to formal smoothness. -/
theorem formallySmooth_iff :
    Algebra.FormallySmooth R A ↔
      Module.Flat (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] Ω[A⁄R]) ∧
        Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A]
          Algebra.H1Cotangent R A) := by
  constructor
  · intro h
    let _ := h
    exact ⟨(LocalCompletionFaithfullyFlat.flat_iff A Ω[A⁄R]).mpr inferInstance,
      (LocalCompletionFaithfullyFlat.subsingleton_iff A (Algebra.H1Cotangent R A)).mpr
        inferInstance⟩
  · rintro ⟨hflat, hzero⟩
    let _ := hflat
    let _ : Module.FinitePresentation A Ω[A⁄R] :=
      Module.finitePresentation_of_finite A Ω[A⁄R]
    exact ⟨LocalCompletionFaithfullyFlat.projective_of_completed_flat A Ω[A⁄R],
      (LocalCompletionFaithfullyFlat.subsingleton_iff A (Algebra.H1Cotangent R A)).mp hzero⟩

/-- For a finitely presented local algebra, the same completed obstruction test gives smoothness. -/
theorem smooth_iff [Algebra.FinitePresentation R A] :
    Algebra.Smooth R A ↔
      Module.Flat (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] Ω[A⁄R]) ∧
        Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A]
          Algebra.H1Cotangent R A) := by
  constructor
  · intro h
    let _ := h
    exact (formallySmooth_iff R A).mp inferInstance
  · intro h
    exact ⟨(formallySmooth_iff R A).mpr h, inferInstance⟩

end FLT.Mazur.LocalCompletionSmoothCriterion
