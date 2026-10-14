/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteCoefficientPointSection
public import FLT.Mazur.EllipticResolvedSmoothPoint

/-!
# Equality of actual specializations descends through the modification tower

Equality at a later finite stage implies equality at every earlier stage.
This supplies the comparison needed to distinguish primitive depths using
their original divided coordinates at the smaller stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Closed-point equality contracts through one actual modification step. -/
theorem finitePointSpecialization_eq_previous (j : ℕ) (hj : j + 1 ≤ n)
    (he : finitePointSpecialization A hπ data (j + 1) hj P =
      finitePointSpecialization A hπ data (j + 1) hj Q) :
    finitePointSpecialization A hπ data j (Nat.le_of_succ_le hj) P =
      finitePointSpecialization A hπ data j (Nat.le_of_succ_le hj) Q := by
  change finiteCoefficientPointSection A hπ data (j + 1) hj (ResidueField A) P =
    finiteCoefficientPointSection A hπ data (j + 1) hj (ResidueField A) Q at he
  change finiteCoefficientPointSection A hπ data j (Nat.le_of_succ_le hj) (ResidueField A) P =
    finiteCoefficientPointSection A hπ data j (Nat.le_of_succ_le hj) (ResidueField A) Q
  have hp := congrArg (· ≫ pullback.snd _ _ ≫ finiteGlobalStep hπ data j hj) he
  rw [finiteCoefficientPointSection_projection_assoc,
    finiteCoefficientPointSection_projection_assoc,
    finitePointSection_step, finitePointSection_step] at hp
  apply pullback.hom_ext
  · rw [finiteCoefficientPointSection_structure, finiteCoefficientPointSection_structure]
  · simpa only [finiteCoefficientPointSection_projection] using hp

/-- Equality at any later finite stage implies equality at every earlier stage. -/
theorem finitePointSpecialization_eq_of_le (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n)
    (hij : i ≤ j)
    (he : finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj Q) :
    finitePointSpecialization A hπ data i hi P =
      finitePointSpecialization A hπ data i hi Q := by
  induction j, hij using Nat.le_induction with
  | base => exact he
  | succ j hij ih =>
    exact ih (Nat.le_of_succ_le hj) (finitePointSpecialization_eq_previous A hπ data j hj he)

/-- Equality in the resolved smooth fiber is visible at every original divided stage. -/
theorem resolvedSplitSmoothPoint_eq_at_stage {depth : ℕ} (D : SplitNodeDepth W π depth)
    (j : ℕ) (hj : j ≤ depth / 2)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    finitePointSpecialization A D.uniformizer_ne_zero (splitResolutionData A D) j hj P =
      finitePointSpecialization A D.uniformizer_ne_zero (splitResolutionData A D) j hj Q := by
  apply finitePointSpecialization_eq_of_le A D.uniformizer_ne_zero (splitResolutionData A D)
    j (depth / 2) hj (le_refl _) hj
  exact (resolvedSplitSmoothPoint_eq_iff A D P Q).mp he

end FLT.Mazur.WeierstrassDividedDepth
