/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerH1Bound

/-!
# Propagation of higher vanishing along a finite divisor

The actual divisor transition is surjective in every positive cohomological
degree. Thus vanishing of structure cohomology in a given positive degree
implies vanishing for every nonnegative power of the divisor line.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]

/-- Positive cohomology vanishing survives an actual finite divisor twist. -/
theorem divisorTwist_positive_subsingleton {L : X.Modules} (hL : LocallyFreeRankOne L)
    (q : ℕ) (hq : 0 < q) [Subsingleton (ModuleScalarH f L q)] :
    Subsingleton (ModuleScalarH f (tensor (divisorLineBundle I hI) L) q) := by
  let e : ModuleScalarH f L q ≃ₗ[k] ModuleScalarH f (tensor (structureModule X) L) q :=
    ((moduleScalarHFunctor f q).mapIso (leftUnitor L).symm).toLinearEquiv
  exact ((divisorTwisted_transition_cohomology_surjective f hI hL q hq).comp
    e.surjective).subsingleton

/-- Structure vanishing in a positive degree propagates through every divisor power. -/
theorem divisorPower_positive_subsingleton (q : ℕ) (hq : 0 < q)
    [Subsingleton (ModuleScalarH f (structureModule X) q)] (m : ℕ) :
    Subsingleton (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) q) := by
  induction m with
  | zero => assumption
  | succ m ih =>
    let _ := ih
    exact divisorTwist_positive_subsingleton f hI
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m) q hq

end FLT.Mazur.FCurve
