/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteYBoundary

/-!
# The full original Y-boundary is compatible with every finite step

The unique lift through an unchanged open identifies successive boundary
maps. Cancellation of their full original-affine pullbacks proves that the
whole Y-boundary, rather than merely its displayed section, is retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
open WeierstrassIntegralChart

omit [IsBezout R] in
/-- The finite affine contraction is the preceding contraction after the actual finite step. -/
theorem finiteToAffine_succ :
    finiteToAffine hπ data (j + 1) hj =
      finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
        finiteToAffine hπ data j (Nat.le_of_succ_le hj) := by
  simp only [finiteToAffine, finiteContraction, Category.assoc]

/-- The actual finite step retains the exact original boundary map. -/
@[reassoc] theorem finiteYBoundary_step :
    finiteYBoundary hπ data (j + 1) hj ≫
        finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj =
      finiteYBoundary hπ data j (Nat.le_of_succ_le hj) := by
  apply SchemeUnchangedOpen.lift_unique
  rw [Category.assoc, ← finiteToAffine_succ, finiteYBoundary_contraction]

/-- The identity on the full original Y-boundary is cartesian for the actual finite step. -/
theorem finiteYBoundary_step_isPullback :
    IsPullback (𝟙 _) (finiteYBoundary hπ data (j + 1) hj)
      (finiteYBoundary hπ data j (Nat.le_of_succ_le hj))
      (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj) := by
  have H : IsPullback ((𝟙 (overlapScheme W 2 1)) ≫ 𝟙 _)
      (finiteYBoundary hπ data (j + 1) hj) (overlapInclusion W 2 1)
      (finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
        finiteToAffine hπ data j (Nat.le_of_succ_le hj)) := by
    rw [Category.id_comp, ← finiteToAffine_succ]
    exact finiteYBoundary_isPullback hπ data (j + 1) hj
  exact H.of_right (by simp only [Category.id_comp, finiteYBoundary_step])
    (finiteYBoundary_isPullback hπ data j (Nat.le_of_succ_le hj))

/-- There are no further points over the old Y-boundary under any actual finite step. -/
theorem finiteYBoundary_step_preimage :
    finiteStep hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ⁻¹'
        Set.range (finiteYBoundary hπ data j (Nat.le_of_succ_le hj)) =
      Set.range (finiteYBoundary hπ data (j + 1) hj) := by
  have H := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (finiteYBoundary_step_isPullback hπ data j hj) ⊤
  simpa [finiteModification] using (congrArg SetLike.coe H).symm

end FLT.Mazur.WeierstrassDividedDepth
