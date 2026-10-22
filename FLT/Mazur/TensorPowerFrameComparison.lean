/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleFrameComparisonUnit
public import FLT.Mazur.TensorPowerGeneratorOpen

/-!
# Exact transition units for powers of an original line

The transition of the nth tensor frame is the nth power of the actual line
transition. These units satisfy the identity and triple-frame cocycle over
arbitrary bases, without any reducedness or characteristic assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} {L : X.Modules}
  (e f g : L ≅ structureModule X)

/-- A frame has identity transition to itself. -/
theorem frameComparisonUnit_self (U : X.Opens) : frameComparisonUnit e e U = 1 := by
  apply Units.ext
  exact sectionIso_hom_inv e U (1 : Γ(X, U))

/-- The exact frame units satisfy the triple-overlap cocycle. -/
theorem frameComparisonUnit_cocycle (U : X.Opens) :
    frameComparisonUnit e f U * frameComparisonUnit f g U = frameComparisonUnit e g U := by
  apply Units.ext
  exact (frame_comparison_apply e f U (g.inv.app U (1 : Γ(X, U)))).symm

/-- Reversing the two retained frames inverts their actual transition. -/
theorem frameComparisonUnit_reverse (U : X.Opens) :
    frameComparisonUnit f e U = (frameComparisonUnit e f U)⁻¹ := by
  apply Units.ext
  rfl

/-- The transition of tensor frames is exactly the corresponding power of the line unit. -/
theorem tensorPowerFrameComparisonUnit (n : ℕ) :
    frameComparisonUnit (tensorPowerTrivialization e n)
      (tensorPowerTrivialization f n) ⊤ = frameComparisonUnit e f ⊤ ^ n := by
  let v := tensorPowerSection L ⊤ (f.inv.app ⊤ (1 : Γ(X, ⊤))) n
  have hv : (tensorPowerTrivialization f n).hom.app ⊤ v = (1 : Γ(X, ⊤)) := by
    rw [tensorPowerTrivialization_section, sectionIso_hom_inv, one_pow]
  apply Units.ext
  rw [← frameComparisonUnit_of_coefficient_one _ _ ⊤ v hv]
  exact tensorPowerTrivialization_section e _ n

/-- Every section, including one with nonunit coordinate, obeys the tensor-frame change. -/
theorem tensorPowerFrameComparison_apply (n : ℕ) (v : Γ(tensorPower L n, ⊤)) :
    (tensorPowerTrivialization e n).hom.app ⊤ v =
      (frameComparisonUnit e f ⊤ : Γ(X, ⊤)) ^ n *
        (show Γ(X, ⊤) from (tensorPowerTrivialization f n).hom.app ⊤ v) := by
  rw [frameComparisonUnit_apply, tensorPowerFrameComparisonUnit, Units.val_pow_eq_pow_val]

end FLT.Mazur.FCurve
