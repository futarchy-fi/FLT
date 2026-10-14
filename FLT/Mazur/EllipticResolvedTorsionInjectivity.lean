/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedAdditionCongruence

/-!
# Injectivity on arbitrary torsion points of the actual resolved smooth fiber

Unrestricted translation congruence reduces equality of two specialized
torsion points to the proved identity-fiber rigidity. Neither input is
assumed to have smooth reduction on the original cubic or a specified label.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Equal actual resolved points give a difference in the actual identity fiber. -/
theorem resolvedSplitSmoothPoint_difference_eq_zero
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    resolvedSplitSmoothPoint A D (P - Q) = resolvedSplitSmoothPoint A D 0 := by
  have ht := (resolvedSplitSmoothPoint_translation_eq_iff A D (-Q)).mpr he
  simpa only [← sub_eq_add_neg, sub_self] using ht

variable [IsAdicComplete (maximalIdeal A) A]

/-- Prime-to-residue torsion points are distinguished by actual resolved specialization. -/
theorem resolvedSplitSmoothPoint_torsion_injective
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m)
    (hP : m • P = 0) (hQ : m • Q = 0)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) : P = Q := by
  apply sub_eq_zero.mp
  apply finitePointSpecialization_torsion_eq_zero A D.uniformizer_ne_zero
    (splitResolutionData A D) (n / 2) (le_refl _) p m hm (P - Q)
  · rw [nsmul_sub, hP, hQ, sub_self]
  · exact (resolvedSplitSmoothPoint_eq_iff A D (P - Q) 0).mp
      (resolvedSplitSmoothPoint_difference_eq_zero A D he)

/-- Actual resolved specialization is injective on the entire prime-to-residue torsion set. -/
theorem resolvedSplitSmoothPoint_injOn_torsion
    (p m : ℕ) [CharP (ResidueField A) p] (hm : ¬ p ∣ m) :
    Set.InjOn (resolvedSplitSmoothPoint A D) {P | m • P = 0} := by
  intro P hP Q hQ he
  exact resolvedSplitSmoothPoint_torsion_injective A D p m hm hP hQ he

variable [IsDiscreteValuationRing A]

/-- Arbitrary p-torsion points are separated below the strict ramification bound. -/
theorem resolvedSplitSmoothPoint_small_ramification_injective
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (hr : RaynaudParameters.order (p : A) < p - 1)
    (hP : p • P = 0) (hQ : p • Q = 0)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) : P = Q := by
  apply sub_eq_zero.mp
  apply finitePointSpecialization_small_ramification_eq_zero A D.uniformizer_ne_zero
    (splitResolutionData A D) (n / 2) (le_refl _) p hp0 hr (P - Q)
  · rw [nsmul_sub, hP, hQ, sub_self]
  · exact (resolvedSplitSmoothPoint_eq_iff A D (P - Q) 0).mp
      (resolvedSplitSmoothPoint_difference_eq_zero A D he)

/-- Actual resolved specialization is injective on all p-torsion below the ramification bound. -/
theorem resolvedSplitSmoothPoint_injOn_small_ramification
    (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
    (hr : RaynaudParameters.order (p : A) < p - 1) :
    Set.InjOn (resolvedSplitSmoothPoint A D) {P | p • P = 0} := by
  intro P hP Q hQ he
  exact resolvedSplitSmoothPoint_small_ramification_injective A D p hp0 hr hP hQ he

end FLT.Mazur.WeierstrassDividedDepth
