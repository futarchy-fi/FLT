/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentCharts

/-!
# Canonical labels of the actual resolved component chart family

The identity has label zero, positive branches have their primitive depth,
and negative branches have the complementary depth. These labels biject with
Fin depth; no extra charts are introduced at the even midpoint.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth

/-- The nonnegative label attached to each original geometric component chart. -/
def resolvedComponentLabel {depth : ℕ} : ResolvedComponentIndex depth → ℕ
  | .identity => 0
  | .retainedPositive j _ _ => j
  | .retainedNegative j _ _ => depth - j
  | .terminalPositive _ _ => depth / 2
  | .terminalNegative _ _ => depth - depth / 2
  | .terminalMiddle _ _ => depth / 2

/-- Every component label lies in the original period. -/
theorem resolvedComponentLabel_lt {depth : ℕ} (hd : 0 < depth)
    (i : ResolvedComponentIndex depth) : resolvedComponentLabel i < depth := by
  cases i <;> dsimp only [resolvedComponentLabel] <;> omega

/-- The chart family has no duplicate nonnegative labels. -/
theorem resolvedComponentLabel_injective {depth : ℕ} :
    Function.Injective (@resolvedComponentLabel depth) := by
  intro i j h
  cases i <;> cases j <;> dsimp only [resolvedComponentLabel] at h <;>
    first | contradiction | (congr 1 <;> omega)

/-- Label zero belongs exactly to the original identity chart. -/
theorem resolvedComponentLabel_zero_iff {depth : ℕ} (i : ResolvedComponentIndex depth) :
    resolvedComponentLabel i = 0 ↔ i = .identity := by
  constructor
  · intro h
    apply resolvedComponentLabel_injective
    exact h
  · rintro rfl
    rfl

/-- Every label in the period occurs in the original component chart family. -/
theorem resolvedComponentLabel_surjective {depth : ℕ} (a : Fin depth) :
    ∃ i : ResolvedComponentIndex depth, resolvedComponentLabel i = a.val := by
  by_cases ha : a.val = 0
  · exact ⟨.identity, ha.symm⟩
  by_cases hp : a.val < depth / 2
  · exact ⟨.retainedPositive a.val (by omega) hp, rfl⟩
  by_cases hn : depth - a.val < depth / 2
  · refine ⟨.retainedNegative (depth - a.val) (by omega) hn, ?_⟩
    dsimp only [resolvedComponentLabel]
    omega
  have hk0 : 0 < depth / 2 := by omega
  by_cases hm : 2 * (depth / 2) = depth
  · refine ⟨.terminalMiddle hk0 hm, ?_⟩
    dsimp only [resolvedComponentLabel]
    omega
  have ho : 2 * (depth / 2) < depth := by omega
  by_cases he : a.val = depth / 2
  · exact ⟨.terminalPositive hk0 ho, he.symm⟩
  · refine ⟨.terminalNegative hk0 ho, ?_⟩
    dsimp only [resolvedComponentLabel]
    omega

/-- The actual chart index is canonically equivalent to the nonnegative period labels. -/
def resolvedComponentIndexEquiv {depth : ℕ} (hd : 0 < depth) :
    ResolvedComponentIndex depth ≃ Fin depth :=
  Equiv.ofBijective (fun i => ⟨resolvedComponentLabel i, resolvedComponentLabel_lt hd i⟩)
    ⟨fun _ _ h => resolvedComponentLabel_injective (congrArg Fin.val h), by
      intro a
      obtain ⟨i, hi⟩ := resolvedComponentLabel_surjective a
      exact ⟨i, Fin.ext hi⟩⟩

/-- The canonical finite index has exactly the geometric branch label. -/
theorem resolvedComponentIndexEquiv_val {depth : ℕ} (hd : 0 < depth)
    (i : ResolvedComponentIndex depth) :
    (resolvedComponentIndexEquiv hd i).val = resolvedComponentLabel i := rfl

end FLT.Mazur.WeierstrassDividedDepth
