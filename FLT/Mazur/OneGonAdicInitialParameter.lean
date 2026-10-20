/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterStages
public import FLT.Mazur.OneGonSmoothingRelativeGroup

/-!
# An actual initial roots embedding for the adic character construction

The initial parameter vanishes in its full coefficient quotient. The corrected
arithmetic torus comparison therefore embeds the original roots group into
the actual initial smooth group, including in characteristics dividing n.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) (t : R) (ht : t ∈ I)

include ht in
/-- The original initial quotient kills the actual smoothing parameter. -/
theorem parameter_zero : parameter I t 0 = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [Nat.zero_add, pow_one] using ht

/-- Equality of parameters transports the actual bundled smooth group. -/
def initialBoundaryIso : relativeGroup (0 : StageRing I 0) ≅ stageGroup I t 0 :=
  eqToIso (congrArg (fun a => integralSmoothGroup (equation a)) (parameter_zero I t ht).symm)

end FLT.Mazur.OneGonAdicCharacterTower
