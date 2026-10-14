/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedSpecialization
public import FLT.Mazur.EllipticResolvedTorsionInjectivity

/-!
# Embedding actual specialization classes and arbitrary torsion

The split product homomorphism descends to an injection from the actual
quotient E/E₁. Its torsion restriction is injective under the original
prime-to-residue or small-ramification hypotheses, without an E₀ condition.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing WeierstrassDividedDepth
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  (h6 : W.a₆ = π ^ n * c₆) (r : (ResidueField A)ˣ)
  (hr : r ^ n = nodeWrapParameterUnit D c₆ h6)

/-- Actual specialization classes map to the split product through the proved E₁ kernel. -/
def nodeSpecializationQuotientHom :
    ((W.map (algebraMap A K)).toProjective.Point ⧸ ellipticE1 A W) →+
      ZMod n × Additive (ResidueField A)ˣ :=
  QuotientAddGroup.lift (ellipticE1 A W) (nodeTrivializedSpecialization D c₆ h6 r hr)
    (le_of_eq (nodeTrivializedSpecialization_ker D c₆ h6 r hr).symm)

/-- Evaluating the descended map on an original point recovers its original product coordinates. -/
@[simp] theorem nodeSpecializationQuotientHom_mk
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodeSpecializationQuotientHom D c₆ h6 r hr
      (P : (W.map (algebraMap A K)).toProjective.Point ⧸ ellipticE1 A W) =
      nodeTrivializedSpecialization D c₆ h6 r hr P := rfl

/-- The actual quotient by E₁ embeds in the split product; surjectivity is not needed. -/
theorem nodeSpecializationQuotientHom_injective :
    Function.Injective (nodeSpecializationQuotientHom D c₆ h6 r hr) := by
  apply (QuotientAddGroup.injective_lift_iff _ _ _).mpr
  exact (nodeTrivializedSpecialization_ker D c₆ h6 r hr).symm

/-- Equality of actual specialization classes is precisely equality in the actual resolved fiber. -/
theorem nodeSpecializationQuotient_eq_iff_resolved
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    QuotientAddGroup.mk' (ellipticE1 A W) P = QuotientAddGroup.mk' (ellipticE1 A W) Q ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q := by
  rw [resolvedSplitSmoothPoint_eq_iff_difference A D]
  exact QuotientAddGroup.eq_iff_sub_mem

variable [IsAdicComplete (maximalIdeal A) A]

/-- Split product coordinates distinguish arbitrary prime-to-residue torsion points. -/
theorem nodeTrivializedSpecialization_injOn_torsion
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m) :
    Set.InjOn (nodeTrivializedSpecialization D c₆ h6 r hr) {P | m • P = 0} := by
  intro P hP Q hQ he
  exact resolvedSplitSmoothPoint_torsion_injective A D p m hm hP hQ
    ((nodeTrivializedSpecialization_eq_iff_resolved D c₆ h6 r hr).mp he)

/-- Split product coordinates distinguish all p-torsion below the strict ramification bound. -/
theorem nodeTrivializedSpecialization_injOn_small_ramification [IsDiscreteValuationRing A]
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (hbound : RaynaudParameters.order (p : A) < p - 1) :
    Set.InjOn (nodeTrivializedSpecialization D c₆ h6 r hr) {P | p • P = 0} := by
  intro P hP Q hQ he
  exact resolvedSplitSmoothPoint_small_ramification_injective A D p hp0 hbound hP hQ
    ((nodeTrivializedSpecialization_eq_iff_resolved D c₆ h6 r hr).mp he)

end FLT.Mazur
