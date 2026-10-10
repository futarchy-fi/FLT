/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteStageRetention

/-!
# Retention starting with its first step

The recursively constructed retention can be split at its first step.
Heterogeneous equality records only the associativity of the natural-number
stage index; every morphism is the original exterior inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (hjNext : j + 1 ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j hj
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hjNext))

/-- Equal stage indices give the same actual exterior carrier. -/
theorem finiteExterior_carrier_congr {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    (finiteExterior hπ data E₀ a ha).carrier =
      (finiteExterior hπ data E₀ b hb).carrier := by
  subst b
  rfl

/-- Equal stage indices retain the identical original exterior inclusion. -/
theorem finiteExterior_retained_heq {a b : ℕ} (ha : a + 1 ≤ n) (hb : b + 1 ≤ n)
    (h : a = b) :
    HEq ((finiteExterior hπ data E₀ a (Nat.le_of_succ_le ha)).retained hπ
      (data ⟨a + 1, Nat.lt_succ_of_le ha⟩))
      ((finiteExterior hπ data E₀ b (Nat.le_of_succ_le hb)).retained hπ
        (data ⟨b + 1, Nat.lt_succ_of_le hb⟩)) := by
  subst b
  rfl

/-- Retention through r+1 stages is its first actual inclusion followed by r later inclusions. -/
theorem finiteStageRetained_succ_left (r : ℕ) (hr : j + (r + 1) ≤ n) :
    HEq (finiteStageRetained hπ data j hj (r + 1) hr)
      ((E).retained hπ e ≫
        finiteStageRetained hπ data (j + 1) hjNext r (by omega)) := by
  induction r with
  | zero =>
    simp only [finiteStageRetained, Category.id_comp]
    rfl
  | succ r ih =>
    change HEq
      (finiteStageRetained hπ data j hj (r + 1) (by omega) ≫
        (finiteExterior hπ data E₀ (j + (r + 1)) (by omega)).retained hπ _)
      ((E).retained hπ e ≫
        (finiteStageRetained hπ data (j + 1) hjNext r (by omega) ≫
          (finiteExterior hπ data E₀ (j + 1 + r) (by omega)).retained hπ _))
    rw [← Category.assoc]
    apply heq_comp rfl
      (finiteExterior_carrier_congr hπ data (by omega) (by omega) (by omega))
      (finiteExterior_carrier_congr hπ data (by omega) (by omega) (by omega)) (ih (by omega))
    exact finiteExterior_retained_heq hπ data (by omega) (by omega) (by omega)

end FLT.Mazur.WeierstrassDividedDepth
