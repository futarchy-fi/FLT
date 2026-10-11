/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredPoleBasis

/-!
# Independence of an unbounded family of exact pole orders

Every finite subfamily lies in an initial segment. Thus the finite
exact-order criterion also proves independence of the full sequence.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FilteredPoleBasis
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Independence of all initial segments detects independence of a sequence. -/
theorem linearIndependent_of_initialSegments (v : ℕ → V)
    (hv : ∀ N, LinearIndependent k (fun i : Fin N ↦ v i)) :
    LinearIndependent k v := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro t
  let e : t → Fin (t.sup id + 1) := fun i ↦
    ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  exact (hv _).comp e (fun i j hij ↦ Subtype.ext (congrArg Fin.val hij))

/-- Strictly increasing exact orders give independence of the entire sequence. -/
theorem linearIndependent_of_nat_orders (P : ℕ → Submodule k V) (hP : Monotone P)
    (v : ℕ → V) (d : ℕ → ℕ) (hd : StrictMono d)
    (hv : ∀ i, v i ∈ P (d i)) (hz : ∀ i, v i ≠ 0)
    (he : ∀ i j, j < d i → v i ∉ P j) : LinearIndependent k v := by
  apply linearIndependent_of_initialSegments
  intro N
  exact linearIndependent_of_orders P hP N _ (fun i ↦ d i)
    (fun _ _ hij ↦ hd hij) (fun i ↦ hv i) (fun i ↦ hz i) (fun i j hij ↦ he i j hij)

end FLT.Mazur.FilteredPoleBasis
