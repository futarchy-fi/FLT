/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFiniteKernelEquiv
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# Completed first homology of a finite polynomial presentation

For a finitely presented algebra over a Noetherian target, completion of the
presentation-independent H1 is the kernel of the completed conormal differential.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicPresentationFirstCotangent

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A ι : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FinitePresentation R A] [IsNoetherianRing A] [Finite ι]
  (P : Algebra.Generators R A ι) (I : Ideal A)

omit [IsNoetherianRing A] in
/-- The conormal module of a finite polynomial presentation is finite. -/
theorem conormal_finite : Module.Finite A P.toExtension.Cotangent :=
  Algebra.Extension.Cotangent.finite P.fg_ker_of_finitePresentation

omit [Algebra.FinitePresentation R A] [IsNoetherianRing A] in
/-- The free cotangent space of a finite polynomial presentation is finite. -/
theorem cotangentSpace_finite : Module.Finite A P.toExtension.CotangentSpace :=
  Module.Finite.of_basis P.cotangentSpaceBasis

/-- Noetherianity makes the first homology of the finite presentation a finite module. -/
theorem presentationH1_finite : Module.Finite A P.toExtension.H1Cotangent := by
  let _ := conormal_finite P
  change Module.Finite A (LinearMap.ker P.toExtension.cotangentComplex)
  infer_instance

include P in
/-- Presentation independence gives finiteness of the actual original first homology. -/
theorem h1_finite : Module.Finite A (Algebra.H1Cotangent R A) := by
  let _ := presentationH1_finite P
  exact Module.Finite.of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective

/-- The completed original first homology is the kernel of the completed original complex. -/
def equiv : AdicCompletion I (Algebra.H1Cotangent R A) ≃ₗ[AdicCompletion I A]
    LinearMap.ker (AdicCompletion.map I P.toExtension.cotangentComplex) := by
  let _ := conormal_finite P
  let _ := cotangentSpace_finite P
  exact AdicCompletion.congr I P.equivH1Cotangent.symm ≪≫ₗ
    AdicFiniteKernelEquiv.equiv I P.toExtension.cotangentComplex

/-- On original classes, the comparison retains the original presentation homology inclusion. -/
theorem equiv_of (x : Algebra.H1Cotangent R A) :
    (equiv P I (AdicCompletion.of I (Algebra.H1Cotangent R A) x)).val =
      AdicCompletion.of I P.toExtension.Cotangent (P.equivH1Cotangent.symm x).val := by
  let _ := conormal_finite P
  let _ := cotangentSpace_finite P
  change (AdicFiniteKernelEquiv.equiv I P.toExtension.cotangentComplex
    (AdicCompletion.map I P.equivH1Cotangent.symm.toLinearMap
      (AdicCompletion.of I (Algebra.H1Cotangent R A) x))).val = _
  rw [AdicCompletion.map_of]
  exact AdicFiniteKernelEquiv.equiv_of I P.toExtension.cotangentComplex _

end FLT.Mazur.AdicPresentationFirstCotangent
