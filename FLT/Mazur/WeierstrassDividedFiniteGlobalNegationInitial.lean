/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegationStep
public import FLT.Mazur.WeierstrassDividedGlobalInitialNegation
public import FLT.Mazur.WeierstrassDividedGlobalInitialActionGeometry

/-!
# Retain the exact original inverse and zero section

The global construction agrees with the previously constructed stage-zero
inverse. At every stage the original zero section is fixed, by uniqueness
of its lift through the unchanged infinity chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "M" => finiteGlobalModel hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "i" => finiteNegationInclusion hπ data j hj
local notation "e" => finiteNegationDomainIso hπ data j hj

local notation "C" => finiteNegationCover hπ data j hj

/-- The constructed global negative fixes the same original zero at every finite depth. -/
@[reassoc] theorem finiteGlobalZero_negation :
    finiteGlobalZero hπ data j hj ≫ finiteGlobalNegation hπ data j hj =
      finiteGlobalZero hπ data j hj := by
  apply finiteInfinity_contraction_ext hπ data j hj
  rw [Category.assoc, finiteGlobalNegation_contraction, finiteGlobalZero_contraction_assoc,
    integralCurveZero_negation]
  rfl

/-- Stage zero is exactly the previously constructed inverse, including its exceptional locus. -/
theorem finiteGlobalNegation_initial :
    finiteGlobalNegation hπ data 0 (Nat.zero_le n) =
      (finiteGlobalInitialNegationIso hπ data).hom := by
  apply finiteGlobalInitial_contraction_ext_of_flat hπ data
    (finiteGlobalInitialNegationIso hπ data).hom
  rw [finiteGlobalNegation_contraction, finiteGlobalInitialNegationIso_contraction]

/-- The new stage-zero automorphism is the original initial automorphism. -/
theorem finiteGlobalNegationIso_initial :
    finiteGlobalNegationIso hπ data 0 (Nat.zero_le n) =
      finiteGlobalInitialNegationIso hπ data := by
  apply Iso.ext
  exact finiteGlobalNegation_initial hπ data

end FLT.Mazur.WeierstrassDividedDepth
