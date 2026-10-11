/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerEulerCharacteristic

/-!
# First cohomology decreases along powers of a finite Cartier divisor

The actual divisor exact sequence gives a surjection after each positive
twist. Hence every power has H1 bounded by that of the structure sheaf.
This requires neither integrality nor ampleness, and applies to a single
marked point on a polygon as well as to its smooth generic fiber.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]

/-- The original divisor transition, expressed with the untwisted source coefficient. -/
def divisorTwistH1Map (L : X.Modules) :
    ModuleScalarH f L 1 →ₗ[k] ModuleScalarH f (tensor (divisorLineBundle I hI) L) 1 :=
  (moduleScalarHMap f (divisorTwistedComplex hI L).f 1).comp
    (((moduleScalarHFunctor f 1).mapIso (leftUnitor L).symm).toLinearEquiv.toLinearMap)

/-- The transition is surjective because its quotient is supported on the finite divisor. -/
theorem divisorTwistH1Map_surjective {L : X.Modules} (hL : LocallyFreeRankOne L) :
    Function.Surjective (divisorTwistH1Map f hI L) :=
  (divisorTwisted_transition_cohomology_surjective f hI hL 1 (by decide)).comp
    (((moduleScalarHFunctor f 1).mapIso (leftUnitor L).symm).toLinearEquiv.surjective)

/-- Twisting by the actual finite effective divisor cannot increase H1 dimension. -/
theorem divisorTwist_h1_finrank_le {L : X.Modules} (hL : LocallyFreeRankOne L) :
    Module.finrank k (ModuleScalarH f (tensor (divisorLineBundle I hI) L) 1) ≤
      Module.finrank k (ModuleScalarH f L 1) := by
  let _ := hL.isFinitePresentation
  let _ := proper_coherent_hasFiniteCohomology f L 1
  exact LinearMap.finrank_le_finrank_of_surjective
    (divisorTwistH1Map_surjective f hI hL)

/-- H1 of each tensor power is bounded by the original structure-sheaf H1. -/
theorem divisorPower_h1_finrank_le (m : ℕ) :
    Module.finrank k (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 1) ≤
      Module.finrank k (ModuleScalarH f (structureModule X) 1) := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact (divisorTwist_h1_finrank_le f hI
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)).trans ih

end FLT.Mazur.FCurve
