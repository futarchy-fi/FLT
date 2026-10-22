/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStageObstructionSquare
public import FLT.Mazur.LocalProperIdealTensorCriterion
public import FLT.Mazur.ResidualFlatTargetExtension

/-!
# Residual and local flatness for the actual affine stage square

The categorical stage equivalence carries residual flatness to the actual
stage algebra. Together with stage obstruction vanishing, this proves flatness
of its local target extensions under the proper-ideal local hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.AffineStageResidualCriterion
open AffineStageObstructionSquare
universe u
variable {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra S B] (r : R →+* S) (s : A →+* B)
  (hs : s.comp (algebraMap R A) = (algebraMap S B).comp r)
  (hp : IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom s))

include hs hp in
/-- Residual flatness transports through the actual stage's constructed equivalence. -/
theorem residual_flat (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)] :
    Module.Flat (S ⧸ I.map r) ((S ⧸ I.map r) ⊗[S] B) := by
  let _ := r.toAlgebra
  let _ := IdealResidualFlatBaseChange.flat (M := A) S I
  exact Module.Flat.of_linearEquiv
    ((baseChangeEquiv r s hs hp).toLinearEquiv.baseChange S (S ⧸ I.map r)).symm

variable (T : Type*) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower S B T]
  [IsNoetherianRing S] [IsLocalRing S] [IsNoetherianRing T] [IsLocalRing T]
  [IsLocalHom (algebraMap S T)]

include hp in
/-- The actual affine stage criterion survives an arbitrary flat target extension. -/
theorem flat [Module.Flat B T] (I : Ideal R) (hI : I.map r ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition r s hs I z.val = 0) : Module.Flat S T := by
  let _ := residual_flat r s hs hp I
  let _ := ResidualFlatTargetExtension.flat (R := S) (A := B) T (I.map r)
  apply LocalProperIdealTensorCriterion.flat_of_ideal_injective (S := T) (M := T) (I.map r) hI
  exact IdealInclusionFlatExtension.injective (R := S) (A := B) T (I.map r)
    (inclusion_injective r s hs hp I h)

include hp in
/-- The criterion applies to actual localizations of the later stage algebra. -/
theorem localization_flat (U : Submonoid B) [IsLocalization U T]
    (I : Ideal R) (hI : I.map r ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition r s hs I z.val = 0) : Module.Flat S T := by
  let _ := IsLocalization.flat T U
  exact flat r s hs hp T I hI h

end FLT.Mazur.AffineStageResidualCriterion
