/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.NormalizedQuotientDescent

/-!
# A strict shear for a normalized quotient row

The row `(t,1)` becomes the second coordinate after conjugation by
`[[1,0],[t,1]]`. Reduction is the identity whenever the parameter reduces to zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Deformation.MoritaReconstruction
variable {A B : Type*} [CommRing A] [CommRing B]

/-- The determinant-one frame adapted to the normalized quotient. -/
def normalizedQuotientShear (t : A) : GL (Fin 2) A where
  val := !![1, 0; t, 1]
  inv := !![1, 0; -t, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A normalized parameter in the residue kernel gives a strict frame. -/
theorem normalizedQuotientShear_map (f : A →+* B) (t : A) (ht : f t = 0) :
    Matrix.GeneralLinearGroup.map f (normalizedQuotientShear t) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normalizedQuotientShear, ht]

/-- The eigenrow equation is exactly the fixed-row equation in this frame. -/
theorem normalizedQuotientShear_row (t c : A) (M : GL (Fin 2) A)
    (h : ∀ j, t * M 0 j + M 1 j = c * (if j = 0 then t else 1)) (j : Fin 2) :
    (normalizedQuotientShear t * M * (normalizedQuotientShear t)⁻¹) 1 j =
      if j = 1 then c else 0 := by
  have h0 := h 0
  have h1 := h 1
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, mul_one] at h0 h1
  change (!![1, 0; t, 1] * M.val * !![1, 0; -t, 1]) 1 j = _
  fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h0, h1]

end Deformation.MoritaReconstruction
