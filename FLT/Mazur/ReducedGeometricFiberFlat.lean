/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReducedConstantFiberFlat
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Flatness detected by constant geometric fiber dimension

For a finite module over a reduced ring, it suffices to count dimensions
after algebraically closed field tests. Extension to an algebraic closure
preserves the original field-fiber dimension.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open TensorProduct

namespace FLT.Mazur.ReducedGeometricFiberFlat

universe u
variable {R M : Type u} [CommRing R] [IsReduced R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsReduced R] [Module.Finite R M] in
/-- Constant geometric fiber dimension already determines all field-fiber dimensions. -/
theorem field_dimension_of_geometric (n : ℕ)
    (hd : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Module.finrank K (K ⊗[R] M) = n)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] M) = n := by
  let L := AlgebraicClosure K
  rw [← Module.finrank_baseChange (R := L),
    (AlgebraTensorModule.cancelBaseChange R K L L M).finrank_eq]
  exact hd L

/-- A finite module with constant geometric fiber dimension over a reduced ring is flat. -/
theorem flat_of_constant_geometric_dimension (n : ℕ)
    (hd : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Module.finrank K (K ⊗[R] M) = n) : Module.Flat R M :=
  ReducedConstantFiberFlat.flat_of_constant_field_dimension n
    (field_dimension_of_geometric n hd)

end FLT.Mazur.ReducedGeometricFiberFlat
