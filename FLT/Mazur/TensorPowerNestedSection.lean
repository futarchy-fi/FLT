/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPowers

/-!
# Flattening nested powers of the original section

The existing exponent-multiplication isomorphism preserves the actual pure
power of a section, including degree zero.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) (U : X.Opens) (s : Γ(L, U))

/-- The actual nested tensor power flattens to the pure power in the product degree. -/
theorem tensorPowerMulIso_powerSection (d n : ℕ) :
    (tensorPowerMulIso L d n).hom.app U
      (tensorPowerSection (tensorPower L d) U (tensorPowerSection L U s d) n) =
        tensorPowerSection L U s (d * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tensorPowerSection, SectionGradedPowers.mulIso_cons, ih,
      SectionGradedMultiplication.mul_power]
    exact SectionGradedMultiplication.cast_power L U s (by rw [Nat.mul_succ, Nat.add_comm])

end FLT.Mazur.FCurve
