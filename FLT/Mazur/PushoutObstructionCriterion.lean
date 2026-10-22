/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineObstructionEquiv
public import FLT.Mazur.LocalProperIdealTensorCriterion
public import FLT.Mazur.ResidualFlatTargetExtension
public import Mathlib.RingTheory.IsTensorProduct

/-!
# The ideal obstruction criterion for an actual pushout square

The canonical pushout equivalence identifies the stage algebra with its scalar
extension. Both residual flatness and the original obstruction transition are
transported through that equivalence before applying the local criterion.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.PushoutObstructionCriterion
variable {R A S B : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B] [Algebra S B] [Algebra A B]
  [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsPushout R S A B]

omit [Algebra.IsPushout R S A B] in
/-- The ring maps of the actual stage square commute. -/
theorem square : (algebraMap A B).comp (algebraMap R A) =
    (algebraMap S B).comp (algebraMap R S) := by
  rw [← IsScalarTower.algebraMap_eq R A B, ← IsScalarTower.algebraMap_eq R S B]

/-- The canonical pushout equivalence identifies the original algebra map. -/
theorem equiv_right (a : A) :
    Algebra.IsPushout.equiv R S A B (AffineObstructionBaseChange.rightMap S a) =
      algebraMap A B a := by
  change Algebra.IsPushout.equiv R S A B (1 ⊗ₜ[R] a) = _
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]

/-- Residual flatness survives the actual stage pushout. -/
theorem residual_flat (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)] :
    Module.Flat (S ⧸ I.map (algebraMap R S))
      ((S ⧸ I.map (algebraMap R S)) ⊗[S] B) := by
  let _ := IdealResidualFlatBaseChange.flat (M := A) S I
  exact Module.Flat.of_linearEquiv
    ((Algebra.IsPushout.equiv R S A B).toLinearEquiv.baseChange
      S (S ⧸ I.map (algebraMap R S))).symm

/-- Killing the original obstruction in the actual pushout proves the new ideal test. -/
theorem inclusion_injective (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S) (algebraMap A B) square I z.val = 0) :
    Function.Injective (FCurve.idealTensorInclusion (S := B) (I.map (algebraMap R S))) :=
  AffineObstructionEquiv.inclusion_injective (Algebra.IsPushout.equiv R S A B)
    (algebraMap A B) square equiv_right I h

variable (T : Type*) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower S B T]
  [IsNoetherianRing S] [IsLocalRing S] [IsNoetherianRing T] [IsLocalRing T]
  [IsLocalHom (algebraMap S T)]

/-- A flat target extension of the actual stage satisfies the local flatness criterion. -/
theorem flat [Module.Flat B T] (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S) (algebraMap A B) square I z.val = 0) :
    Module.Flat S T := by
  let _ := residual_flat (A := A) (S := S) (B := B) I
  let _ := ResidualFlatTargetExtension.flat (R := S) (A := B) T (I.map (algebraMap R S))
  apply LocalProperIdealTensorCriterion.flat_of_ideal_injective
    (S := T) (M := T) (I.map (algebraMap R S)) hI
  exact IdealInclusionFlatExtension.injective (R := S) (A := B) T
    (I.map (algebraMap R S)) (inclusion_injective I h)

/-- In particular the actual-stage criterion applies to its localizations. -/
theorem localization_flat (U : Submonoid B) [IsLocalization U T]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S) (algebraMap A B) square I z.val = 0) :
    Module.Flat S T := by
  let _ := IsLocalization.flat T U
  exact flat T I hI h

end FLT.Mazur.PushoutObstructionCriterion
