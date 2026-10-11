/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityNodeFamily

/-!
# Positive-start branch indices, including the original initial nodes

Each branch starts at its initial node and continues through every retained
node. The two branches exhaust the equality-depth attachment family.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Attachments along one branch, from the initial node to the terminal conic. -/
def positiveEqualityBranchNode (start s : ℕ) (hstart : 0 < start)
    (j : Fin (s + 2)) (i : Fin 2) : EqualityNodeIndex start s :=
  if h : j.val = 0 then .inl ⟨i, hstart⟩ else .inr (⟨j.val - 1, by omega⟩, i)

/-- The first branch attachment is the original initial node. -/
theorem positiveEqualityBranchNode_initial (start s : ℕ) (hstart : 0 < start)
    (i : Fin 2) :
    positiveEqualityBranchNode start s hstart 0 i = .inl ⟨i, hstart⟩ := by
  simp only [positiveEqualityBranchNode, Fin.val_zero, dite_true]

/-- Every subsequent attachment is the corresponding original retained node. -/
theorem positiveEqualityBranchNode_retained (start s : ℕ) (hstart : 0 < start)
    (j : Fin (s + 1)) (i : Fin 2) :
    positiveEqualityBranchNode start s hstart ⟨j.val + 1, by omega⟩ i = .inr (j, i) := by
  rw [positiveEqualityBranchNode, dite_eq_right (show ¬j.val + 1 = 0 by omega)]
  rfl

/-- Neither the initial stage nor the tangent order is lost in branch indexing. -/
theorem positiveEqualityBranchNode_injective (start s : ℕ) (hstart : 0 < start) :
    Function.Injective (fun a : Fin (s + 2) × Fin 2 =>
      positiveEqualityBranchNode start s hstart a.1 a.2) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ he
  change positiveEqualityBranchNode start s hstart j i =
    positiveEqualityBranchNode start s hstart k l at he
  by_cases hj : j.val = 0 <;> by_cases hk : k.val = 0
  · rw [positiveEqualityBranchNode, dite_eq_left hj,
      positiveEqualityBranchNode, dite_eq_left hk] at he
    exact Prod.ext (Fin.ext (hj.trans hk.symm)) (congrArg Subtype.val (Sum.inl.inj he))
  · rw [positiveEqualityBranchNode, dite_eq_left hj,
      positiveEqualityBranchNode, dite_eq_right hk] at he
    cases he
  · rw [positiveEqualityBranchNode, dite_eq_right hj,
      positiveEqualityBranchNode, dite_eq_left hk] at he
    cases he
  · rw [positiveEqualityBranchNode, dite_eq_right hj,
      positiveEqualityBranchNode, dite_eq_right hk] at he
    obtain ⟨hjk, hil⟩ := Prod.mk.inj (Sum.inr.inj he)
    have H := congrArg Fin.val hjk
    change j.val - 1 = k.val - 1 at H
    have hjk' : j = k := Fin.ext (show j.val = k.val by omega)
    exact Prod.ext hjk' hil

/-- The branch indices include every original initial and retained attachment. -/
theorem positiveEqualityBranchNode_surjective (start s : ℕ) (hstart : 0 < start) :
    Function.Surjective (fun a : Fin (s + 2) × Fin 2 =>
      positiveEqualityBranchNode start s hstart a.1 a.2) := by
  rintro (⟨i, hi⟩ | ⟨j, i⟩)
  · exact ⟨(0, i), positiveEqualityBranchNode_initial start s hstart i⟩
  · exact ⟨(⟨j.val + 1, by omega⟩, i),
      positiveEqualityBranchNode_retained start s hstart j i⟩

/-- The actual equality-depth attachments are exactly the two full branches. -/
def positiveEqualityBranchNodeEquiv (start s : ℕ) (hstart : 0 < start) :
    (Fin (s + 2) × Fin 2) ≃ EqualityNodeIndex start s :=
  Equiv.ofBijective (fun a => positiveEqualityBranchNode start s hstart a.1 a.2)
    ⟨positiveEqualityBranchNode_injective start s hstart,
      positiveEqualityBranchNode_surjective start s hstart⟩

end FLT.Mazur.WeierstrassDividedDepth
