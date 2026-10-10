/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorProper
public import FLT.Mazur.WeierstrassDividedFiniteContraction

/-!
# Properness throughout arbitrary finite divided-depth iteration

Every actual whole step is proper, for any retained exterior. Their finite
composites are therefore proper, with the existing coordinate contractions
and unchanged exterior supplied by the original iteration construction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (E : Exterior (data ⟨0, Nat.zero_lt_succ n⟩))

/-- Each actual whole step is proper, including its full retained exterior. -/
theorem finiteStep_isProper (j : ℕ) (hj : j + 1 ≤ n) :
    IsProper (finiteStep hπ data E j hj) :=
  (finiteExterior hπ data E j (Nat.le_of_succ_le hj)).stepContraction_isProper hπ
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)

/-- Every finite composite contracts properly to the initial whole scheme. -/
theorem finiteContraction_isProper (j : ℕ) (hj : j ≤ n) :
    IsProper (finiteContraction hπ data E j hj) := by
  induction j with
  | zero => change IsProper (𝟙 E.whole); infer_instance
  | succ j ih =>
    let _ := ih (Nat.le_of_succ_le hj)
    let _ := finiteStep_isProper hπ data E j hj
    change IsProper (finiteStep hπ data E j hj ≫
      finiteContraction hπ data E j (Nat.le_of_succ_le hj))
    infer_instance

/-- Properness to any base is retained by the actual finite iteration. -/
theorem finiteContraction_comp_isProper {S : Scheme} (f : E.whole ⟶ S) [IsProper f]
    (j : ℕ) (hj : j ≤ n) : IsProper (finiteContraction hπ data E j hj ≫ f) := by
  let _ := finiteContraction_isProper hπ data E j hj
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
