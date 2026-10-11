/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithful detection by the actual local completion

For a Noetherian local ring, the canonical maximal-ideal completion is
faithfully flat. Scalar extension to this completion detects vanishing and
flatness of modules, and hence projectivity of finitely presented modules.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.LocalCompletionFaithfullyFlat

variable (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- The canonical completion of a Noetherian local ring is faithfully flat. -/
theorem faithfullyFlat :
    Module.FaithfullyFlat A (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

variable (M : Type*) [AddCommGroup M] [Module A M]

/-- A module vanishes if and only if its extension to the actual completion vanishes. -/
theorem subsingleton_iff :
    Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] M) ↔
      Subsingleton M := by
  let _ := faithfullyFlat A
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A _

/-- Flatness is detected after extension to the actual maximal-ideal completion. -/
theorem flat_iff :
    Module.Flat (AdicCompletion (IsLocalRing.maximalIdeal A) A)
        (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] M) ↔
      Module.Flat A M := by
  let _ := faithfullyFlat A
  exact Module.Flat.iff_flat_tensorProduct A M _

/-- Completed flatness forces a finitely presented module to be projective. -/
theorem projective_of_completed_flat [Module.FinitePresentation A M]
    [Module.Flat (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] M)] :
    Module.Projective A M := by
  let _ := (flat_iff A M).mp inferInstance
  exact Module.Flat.projective_of_finitePresentation

end FLT.Mazur.LocalCompletionFaithfullyFlat
