/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteYStep
public import FLT.Mazur.WeierstrassDividedGlobalFiniteZero

/-!
# Proper steps between the whole finite projective models

Glue each existing finite local step to the identity of the original chart
at infinity. Full boundary pullbacks prove properness of these actual global
steps, and their contractions and retained zero points agree exactly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
open WeierstrassIntegralChart

/-- The existing finite local step glued to the identity of the original infinity chart. -/
def finiteGlobalStep : finiteGlobalModel hπ data (j + 1) hj ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj) :=
  SchemeOpenReplacement.contraction (affineBoundaryToY W)
    (finiteYBoundary hπ data j (Nat.le_of_succ_le hj))
    (finiteYBoundary hπ data (j + 1) hj)
    (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj)
    (finiteYBoundary_step hπ data j hj)

/-- Every global step retains the entire original chart at infinity. -/
@[reassoc] theorem finiteGlobalStep_infinity :
    finiteInfinityChart hπ data (j + 1) hj ≫ finiteGlobalStep hπ data j hj =
      finiteInfinityChart hπ data j (Nat.le_of_succ_le hj) :=
  SchemeOpenReplacement.inl_contraction _ _ _ _ _

/-- Every global step retains exactly the existing finite local step. -/
@[reassoc] theorem finiteGlobalStep_local :
    finiteLocalChart hπ data (j + 1) hj ≫ finiteGlobalStep hπ data j hj =
      finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
        finiteLocalChart hπ data j (Nat.le_of_succ_le hj) :=
  SchemeOpenReplacement.inr_contraction _ _ _ _ _

/-- The actual global step is proper, using the full original boundary pullback. -/
instance finiteGlobalStep_isProper : IsProper (finiteGlobalStep hπ data j hj) := by
  let _ := finiteStep_isProper hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj
  exact SchemeOpenReplacement.contraction_isProper _ _ _ _ _
    (finiteYBoundary_step_preimage hπ data j hj)

/-- The global steps commute with the actual contractions to the original projective cubic. -/
@[reassoc] theorem finiteGlobalStep_contraction :
    finiteGlobalStep hπ data j hj ≫
        finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
      finiteGlobalContraction hπ data (j + 1) hj := by
  apply pushout.hom_ext
  · change finiteInfinityChart hπ data (j + 1) hj ≫ _ =
      finiteInfinityChart hπ data (j + 1) hj ≫ _
    rw [finiteGlobalStep_infinity_assoc, finiteInfinityChart_contraction,
      finiteInfinityChart_contraction]
  · change finiteLocalChart hπ data (j + 1) hj ≫ _ =
      finiteLocalChart hπ data (j + 1) hj ≫ _
    rw [finiteGlobalStep_local_assoc, finiteLocalChart_contraction,
      finiteLocalChart_contraction]
    simp only [finiteToCurve, finiteContraction, Category.assoc]

/-- Every proper global step preserves the exact original zero point. -/
@[reassoc] theorem finiteGlobalStep_zero :
    finiteGlobalZero hπ data (j + 1) hj ≫ finiteGlobalStep hπ data j hj =
      finiteGlobalZero hπ data j (Nat.le_of_succ_le hj) := by
  rw [finiteGlobalZero, Category.assoc, finiteGlobalStep_infinity]
  rfl

/-- The proper global steps are morphisms over the original coefficient scheme. -/
@[reassoc] theorem finiteGlobalStep_structure :
    finiteGlobalStep hπ data j hj ≫
        finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj) =
      finiteGlobalStructure hπ data (j + 1) hj := by
  rw [finiteGlobalStructure, finiteGlobalStep_contraction_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
