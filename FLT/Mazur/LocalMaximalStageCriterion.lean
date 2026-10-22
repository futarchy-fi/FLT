/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStageResidualCriterion

/-!
# Local maximal-ideal obstruction tests for actual affine stages

For a local old base, the residual algebra is a module over its residue field
and is automatically flat. A local base transition preserves properness of the
extended old maximal ideal. These facts discharge two hypotheses of the actual
stage criterion without replacing that extended ideal by the new maximal ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.LocalMaximalStageCriterion
universe u
variable {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra S B] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
  (r : R →+* S) [IsLocalHom r] (s : A →+* B)
  (hs : s.comp (algebraMap R A) = (algebraMap S B).comp r)
  (hp : IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom s))
  (T : Type*) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower S B T]
  [IsLocalRing T] [IsNoetherianRing T] [IsLocalHom (algebraMap S T)]

include hp in
/-- The residue field and local base map discharge residual flatness and properness. -/
theorem flat [Module.Flat B T]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) (IsLocalRing.maximalIdeal R),
      IdealTensorKernel.transition r s hs (IsLocalRing.maximalIdeal R) z.val = 0) :
    Module.Flat S T := by
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  apply AffineStageResidualCriterion.flat r s hs hp T (IsLocalRing.maximalIdeal R)
    (IsLocalRing.map_maximalIdeal_lt_top r).ne h

include hp in
/-- This specializes to localizations of the actual stage algebra. -/
theorem localization_flat (U : Submonoid B) [IsLocalization U T]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) (IsLocalRing.maximalIdeal R),
      IdealTensorKernel.transition r s hs (IsLocalRing.maximalIdeal R) z.val = 0) :
    Module.Flat S T := by
  let _ := IsLocalization.flat T U
  exact flat r s hs hp T h

end FLT.Mazur.LocalMaximalStageCriterion
