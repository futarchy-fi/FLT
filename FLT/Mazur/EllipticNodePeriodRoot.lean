/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedSpecialization
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Period roots over an algebraically closed residue field

Algebraic closedness constructs a nonzero n-th root of the original period.
Choosing one gives split product coordinates for the actual specialization.
Different roots change the parameter by their explicit componentwise ratio.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A) (h6 : W.a₆ = π ^ n * c₆)

/-- Two possible period roots differ by an n-torsion unit. -/
theorem nodePeriodRoot_ratio_pow (r s : (ResidueField A)ˣ)
    (hr : r ^ n = nodeWrapParameterUnit D c₆ h6)
    (hs : s ^ n = nodeWrapParameterUnit D c₆ h6) : (r / s) ^ n = 1 := by
  rw [div_pow, hr, hs, div_self']

/-- Changing the root changes the parameter by the corresponding power on each component. -/
theorem nodeTrivializedParameter_change_root (r s : (ResidueField A)ˣ)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodeTrivializedParameter D c₆ h6 s P =
      nodeTrivializedParameter D c₆ h6 r P * (r / s) ^ (nodePointLabel D P).val := by
  dsimp only [nodeTrivializedParameter]
  rw [div_pow, div_mul_div_cancel]

variable [IsAlgClosed (ResidueField A)]

/-- The actual nonzero period has a unit n-th root over an algebraically closed residue field. -/
theorem exists_nodePeriodRoot :
    ∃ r : (ResidueField A)ˣ, r ^ n = nodeWrapParameterUnit D c₆ h6 := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (nodeWrapParameter W c₆) D.depth_pos
  have hn : r ≠ 0 := by
    intro hz
    apply nodeWrapParameter_ne_zero D c₆ h6
    rw [← hr, hz, zero_pow (Nat.ne_of_gt D.depth_pos)]
  refine ⟨Units.mk0 r hn, ?_⟩
  apply Units.ext
  exact hr

/-- A chosen actual period root; it is not asserted to be canonical. -/
def nodePeriodRoot : (ResidueField A)ˣ := (exists_nodePeriodRoot D c₆ h6).choose

/-- The chosen root retains the original period coefficient. -/
theorem nodePeriodRoot_pow : nodePeriodRoot D c₆ h6 ^ n = nodeWrapParameterUnit D c₆ h6 :=
  (exists_nodePeriodRoot D c₆ h6).choose_spec

/-- Split product specialization using a constructed residue-field period root. -/
def nodeSplitParameterSpecialization :
    (W.map (algebraMap A K)).toProjective.Point →+ ZMod n × Additive (ResidueField A)ˣ :=
  nodeTrivializedSpecialization D c₆ h6 (nodePeriodRoot D c₆ h6) (nodePeriodRoot_pow D c₆ h6)

/-- This constructed split presentation still detects the actual resolved points. -/
theorem nodeSplitParameterSpecialization_eq_iff_resolved
    {P Q : (W.map (algebraMap A K)).toProjective.Point} :
    nodeSplitParameterSpecialization D c₆ h6 P = nodeSplitParameterSpecialization D c₆ h6 Q ↔
      WeierstrassDividedDepth.resolvedSplitSmoothPoint A D P =
        WeierstrassDividedDepth.resolvedSplitSmoothPoint A D Q :=
  nodeTrivializedSpecialization_eq_iff_resolved D c₆ h6 _ _

end FLT.Mazur
