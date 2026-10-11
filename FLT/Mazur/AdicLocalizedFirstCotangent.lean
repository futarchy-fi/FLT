/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicPresentationFirstCotangent
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Completed first homology at a localization of a finite presentation

An actual localized algebra has first homology computed by the localized
conormal complex. Completing this complex computes completion of its original H1.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicLocalizedFirstCotangent

open TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A ι : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FinitePresentation R A] [IsNoetherianRing A] [Finite ι]
  (P : Algebra.Generators R A ι) (S : Type u) [CommRing S]
  [Algebra A S] [Algebra R S] [IsScalarTower R A S]
  (T : Submonoid A) [IsLocalization T S]

omit [Algebra.FinitePresentation R A] [IsNoetherianRing A] [Finite ι] in
/-- Actual localized first homology is the kernel of the localized original conormal map. -/
def localizedEquiv : Algebra.H1Cotangent R S ≃ₗ[S]
    LinearMap.ker (P.toExtension.cotangentComplex.baseChange S) := by
  let _ := IsLocalization.flat S T
  exact (Algebra.tensorH1CotangentOfIsLocalization R S T).symm ≪≫ₗ
    P.equivH1Cotangent.symm.baseChange A S _ _ ≪≫ₗ
      LinearMap.tensorKerEquiv S S P.toExtension.cotangentComplex

include P T in
/-- Localized original first homology is finite, without finite presentation of the localization. -/
theorem localizedH1_finite : Module.Finite S (Algebra.H1Cotangent R S) := by
  let _ := AdicPresentationFirstCotangent.h1_finite P
  exact Module.Finite.of_surjective
    (Algebra.tensorH1CotangentOfIsLocalization R S T).toLinearMap
    (Algebra.tensorH1CotangentOfIsLocalization R S T).surjective

variable [IsNoetherianRing S] (J : Ideal S)

/-- Completion of actual localized H1 is the kernel of its completed localized conormal map. -/
def completedEquiv : AdicCompletion J (Algebra.H1Cotangent R S) ≃ₗ[AdicCompletion J S]
    LinearMap.ker (AdicCompletion.map J (P.toExtension.cotangentComplex.baseChange S)) := by
  let _ := AdicPresentationFirstCotangent.conormal_finite P
  let _ := AdicPresentationFirstCotangent.cotangentSpace_finite P
  exact AdicCompletion.congr J (localizedEquiv P S T) ≪≫ₗ
    AdicFiniteKernelEquiv.equiv J (P.toExtension.cotangentComplex.baseChange S)

omit [IsNoetherianRing A] in
/-- On original localized classes, completion retains the localized conormal representative. -/
theorem completedEquiv_of (x : Algebra.H1Cotangent R S) :
    (completedEquiv P S T J (AdicCompletion.of J (Algebra.H1Cotangent R S) x)).val =
      AdicCompletion.of J (S ⊗[A] P.toExtension.Cotangent) (localizedEquiv P S T x).val := by
  let _ := AdicPresentationFirstCotangent.conormal_finite P
  let _ := AdicPresentationFirstCotangent.cotangentSpace_finite P
  change (AdicFiniteKernelEquiv.equiv J (P.toExtension.cotangentComplex.baseChange S)
    (AdicCompletion.map J (localizedEquiv P S T).toLinearMap
      (AdicCompletion.of J (Algebra.H1Cotangent R S) x))).val = _
  rw [AdicCompletion.map_of]
  exact AdicFiniteKernelEquiv.equiv_of J (P.toExtension.cotangentComplex.baseChange S) _

end FLT.Mazur.AdicLocalizedFirstCotangent
