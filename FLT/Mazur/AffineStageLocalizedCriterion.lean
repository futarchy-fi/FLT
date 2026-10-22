/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStageLocalizedTarget
public import FLT.Mazur.LocalizedObstructionVanishingCriterion

/-!
# The actual stage criterion with vanishing only in its localized target

The categorical pushout equivalence and its transported target action allow
the localization-only criterion to apply directly to the given stage maps.
No vanishing in the unlocalized pushout is assumed or inferred.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.AffineStageLocalizedCriterion
open AffineStageLocalizedTarget
universe u
variable {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra S B] (r : R →+* S) (s : A →+* B)
  (hs : s.comp (algebraMap R A) = (algebraMap S B).comp r)
  (hp : IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom s))
  (T : Type*) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower S B T]

include hs in
/-- The old algebra's actual composite into the final target retains the base square. -/
theorem target_square : ((algebraMap B T).comp s).comp (algebraMap R A) =
    (algebraMap S T).comp r := by
  rw [RingHom.comp_assoc, hs, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq S B T]

variable [IsNoetherianRing S] [IsLocalRing S] [IsNoetherianRing T] [IsLocalRing T]
  [IsLocalHom (algebraMap S T)]

include hp in
/-- Vanishing in an actual flat target extension suffices for local flatness. -/
theorem flat [Module.Flat B T] (I : Ideal R) (hI : I.map r ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition r ((algebraMap B T).comp s)
        (target_square r s hs T) I z.val = 0) : Module.Flat S T := by
  let _ := r.toAlgebra
  let _ := tensorAlgebra r s hs hp T
  let _ := tensorScalarTower r s hs hp T
  let _ := tensor_flat r s hs hp T
  apply LocalizedObstructionVanishingCriterion.flat (A := A) S T I hI
  intro z
  have he := tensorRightMap_eq r s hs hp T
  dsimp only at he
  have ht (w : A ⊗[R] I) :
      IdealTensorKernel.transition (algebraMap R S)
        (AffineTargetObstructionTransition.rightMap (R := R) S T)
        (AffineTargetObstructionTransition.square S T) I w =
      IdealTensorKernel.transition r ((algebraMap B T).comp s)
        (target_square r s hs T) I w := by
    induction w with
    | tmul a i =>
      simp only [IdealTensorKernel.transition_tmul]
      rw [RingHom.congr_fun he a]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact (ht z.val).trans (h z)

include hp in
/-- In particular the obstruction may vanish only after localizing the actual stage. -/
theorem localization_flat (U : Submonoid B) [IsLocalization U T]
    (I : Ideal R) (hI : I.map r ≠ ⊤)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition r ((algebraMap B T).comp s)
        (target_square r s hs T) I z.val = 0) : Module.Flat S T := by
  let _ := IsLocalization.flat T U
  exact flat r s hs hp T I hI h

include hp in
/-- For a local old base, its residue field discharges the residual-flatness hypothesis. -/
theorem maximal_localization_flat [IsLocalRing R] [IsLocalHom r]
    (U : Submonoid B) [IsLocalization U T]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) (IsLocalRing.maximalIdeal R),
      IdealTensorKernel.transition r ((algebraMap B T).comp s)
        (target_square r s hs T) (IsLocalRing.maximalIdeal R) z.val = 0) :
    Module.Flat S T := by
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  exact localization_flat r s hs hp T U (IsLocalRing.maximalIdeal R)
    (IsLocalRing.map_maximalIdeal_lt_top r).ne h

end FLT.Mazur.AffineStageLocalizedCriterion
