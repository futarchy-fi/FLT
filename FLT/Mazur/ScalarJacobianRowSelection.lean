/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Selecting a nonsingular square system from spanning residue gradients

A possibly infinite family of rows spanning the residue coordinate space
contains a basis. Reindexing that basis selects distinct equations with a
nonzero square determinant, including the zero-coordinate case.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarJacobianRowSelection
open Module
variable {K κ : Type} [Field K] (n : ℕ) (rows : κ → Fin n → K)

/-- Spanning residue rows construct distinct indices with a nonsingular square determinant. -/
theorem exists_nonsingular
    (h : Submodule.span K (Set.range rows) = ⊤) :
    ∃ r : Fin n → κ, Function.Injective r ∧ Matrix.det (fun i j ↦ rows (r i) j) ≠ 0 := by
  classical
  let b := Basis.ofSpan h.ge
  let e := b.indexEquiv (Pi.basisFun K (Fin n))
  let c := b.reindex e
  have hc (i : Fin n) : c i ∈ Set.range rows :=
    Basis.ofSpan_subset h.ge ⟨e.symm i, (b.reindex_apply e i).symm⟩
  choose r hr using hc
  have he : (fun i ↦ rows (r i)) = c := funext hr
  refine ⟨r, ?_, ?_⟩
  · intro i j hij
    apply c.injective
    rw [← hr i, ← hr j, hij]
  · apply Matrix.nonsingular_iff_det_ne_zero.mp
    apply Matrix.Nonsingular.of_linearIndependent_row
    change LinearIndependent K (fun i ↦ rows (r i))
    rw [he]
    exact c.linearIndependent

end FLT.Mazur.ScalarJacobianRowSelection
