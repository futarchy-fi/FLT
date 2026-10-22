/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineObstructionAnnihilator
public import FLT.Mazur.AffineTargetObstructionTransition
public import FLT.Mazur.LocalProperIdealTensorCriterion
public import FLT.Mazur.ResidualFlatTargetExtension

/-!
# Local flatness from obstruction vanishing only after localization

The original obstruction is tested in the final target. Its vanishing there
annihilates the entire scalar-extended obstruction, and flat exactness then
proves the ideal test in that target. No unlocalized vanishing is required.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalizedObstructionVanishingCriterion
open AffineTargetObstructionTransition
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (S T : Type*) [CommRing S] [Algebra R S] [CommRing T] [Algebra S T]
  [Algebra (S ⊗[R] A) T] [IsScalarTower S (S ⊗[R] A) T]

/-- Vanishing only in the flat target extension suffices for its full ideal test. -/
theorem inclusion_injective [Module.Flat (S ⊗[R] A) T] (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S)
        (rightMap (R := R) S T) (square S T) I z.val = 0) :
    Function.Injective (FCurve.idealTensorInclusion (S := T) (I.map (algebraMap R S))) := by
  apply FlatTargetObstructionMap.inclusion_injective (A := S ⊗[R] A) T
  apply AffineObstructionAnnihilator.map_kernel_eq_zero S I
  intro z
  rw [← transition_eq]
  exact h z

variable [IsNoetherianRing S] [IsLocalRing S] [IsNoetherianRing T] [IsLocalRing T]
  [IsLocalHom (algebraMap S T)]

/-- The local proper-ideal criterion applies when the obstruction dies only in the target. -/
theorem flat [Module.Flat (S ⊗[R] A) T] (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S)
        (rightMap (R := R) S T) (square S T) I z.val = 0) :
    Module.Flat S T := by
  let _ := IdealResidualFlatBaseChange.flat (M := A) S I
  let _ := ResidualFlatTargetExtension.flat (R := S) (A := S ⊗[R] A) T
    (I.map (algebraMap R S))
  apply LocalProperIdealTensorCriterion.flat_of_ideal_injective
    (S := T) (M := T) (I.map (algebraMap R S)) hI
  exact inclusion_injective S T I h

/-- Localized vanishing proves flatness of an actual localized affine scalar extension. -/
theorem localization_flat (U : Submonoid (S ⊗[R] A)) [IsLocalization U T]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S)
        (rightMap (R := R) S T) (square S T) I z.val = 0) :
    Module.Flat S T := by
  let _ := IsLocalization.flat T U
  exact flat S T I hI h

end FLT.Mazur.LocalizedObstructionVanishingCriterion
