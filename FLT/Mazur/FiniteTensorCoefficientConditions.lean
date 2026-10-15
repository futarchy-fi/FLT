/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorCoefficientDetection

/-!
# One original coefficient condition for finitely many extended functions

For an integral original affine algebra, finitely many nonzero functions over
an arbitrary extension have one nonzero original coefficient condition.
Every original rational point satisfying it preserves every actual extended
nonvanishing condition. The coefficient field need not be algebraic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TensorCoefficientDetection
open scoped TensorProduct
variable {k K A J : Type*} [Field k] [Field K] [Algebra k K]
  [CommRing A] [IsDomain A] [Algebra k A] [Finite J]

/-- A common original principal condition controls the entire finite family. -/
theorem exists_common_detecting_coefficient (x : J → K ⊗[k] A) (hx : ∀ j, x j ≠ 0) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : A →ₐ[k] k,
      p a ≠ 0 → ∀ j, evaluation (K := K) p (x j) ≠ 0 := by
  classical
  let _ := Fintype.ofFinite J
  choose a ha hd using fun j ↦ exists_nonzero_detecting_coefficient (x j) (hx j)
  refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.mpr (fun j _ ↦ ha j), fun p hp j ↦ ?_⟩
  apply hd j p
  have hp' : (∏ j, p (a j)) ≠ 0 := by simpa only [map_prod] using hp
  exact (Finset.prod_ne_zero_iff.mp hp') j (Finset.mem_univ j)

end FLT.Mazur.TensorCoefficientDetection
