/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineObstructionBaseChange
public import FLT.Mazur.LocalProperIdealTensorCriterion
public import FLT.Mazur.ResidualFlatTargetExtension

/-!
# Local flatness after scalar extension and target localization

Vanishing of the original affine obstruction in the actual tensor algebra
implies the ideal test in every flat target extension. Residual flatness
survives both operations, so the proper-ideal local criterion gives genuine
flatness of the localized algebra over the new local Noetherian base.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalizedAffineObstructionCriterion
open AffineObstructionBaseChange
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (S T : Type*) [CommRing S] [Algebra R S] [IsNoetherianRing S] [IsLocalRing S]
  [CommRing T] [Algebra S T] [IsNoetherianRing T] [IsLocalRing T]
  [IsLocalHom (algebraMap S T)]
  [Algebra (S ⊗[R] A) T] [IsScalarTower S (S ⊗[R] A) T]

/-- Killing the old affine obstruction before a flat target extension proves local flatness. -/
theorem flat [Module.Flat (S ⊗[R] A) T] (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S) (rightMap S) (square S) I z.val = 0) :
    Module.Flat S T := by
  let _ := IdealResidualFlatBaseChange.flat (M := A) S I
  let _ := ResidualFlatTargetExtension.flat (R := S) (A := S ⊗[R] A) T
    (I.map (algebraMap R S))
  apply LocalProperIdealTensorCriterion.flat_of_ideal_injective
    (S := T) (M := T) (I.map (algebraMap R S)) hI
  exact IdealInclusionFlatExtension.injective (R := S) (A := S ⊗[R] A) T
    (I.map (algebraMap R S)) (inclusion_injective S I h)

/-- The criterion applies in particular to any localization of the actual tensor algebra. -/
theorem localization_flat (U : Submonoid (S ⊗[R] A)) [IsLocalization U T]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S) (rightMap S) (square S) I z.val = 0) :
    Module.Flat S T := by
  let _ := IsLocalization.flat T U
  exact flat S T I hI h

end FLT.Mazur.LocalizedAffineObstructionCriterion
