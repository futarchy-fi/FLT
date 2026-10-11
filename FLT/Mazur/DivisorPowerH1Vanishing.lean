/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerH1Bound

/-!
# Acyclicity propagates through positive divisor powers

The surjective maps from the actual divisor sequence propagate first
cohomology vanishing. In particular, checking O(P) suffices for every
positive power O(mP); no ampleness or integrality is needed for propagation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]

/-- The actual finite divisor transition carries H1 vanishing to its target. -/
theorem divisorTwist_h1_subsingleton {L : X.Modules} (hL : LocallyFreeRankOne L)
    [Subsingleton (ModuleScalarH f L 1)] :
    Subsingleton (ModuleScalarH f (tensor (divisorLineBundle I hI) L) 1) :=
  (divisorTwistH1Map_surjective f hI hL).subsingleton

/-- Vanishing for the first point power suffices for every positive point power. -/
theorem divisorPower_h1_subsingleton_of_first
    (hfirst : Subsingleton (ModuleScalarH f (tensorPower (divisorLineBundle I hI) 1) 1))
    (m : ℕ) :
    Subsingleton (ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 1) := by
  induction m with
  | zero => exact hfirst
  | succ m ih =>
    let _ := ih
    exact divisorTwist_h1_subsingleton f hI
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower (m + 1))

end FLT.Mazur.FCurve
