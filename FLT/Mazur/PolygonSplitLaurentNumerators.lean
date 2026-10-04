/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicTorusNumerators

/-!
# Numerators at the two distinct branches of a split node

The successor and predecessor inequalities are proved from n ≥ 2; no branch
is discarded for a two-gon. The successor formulas use Laurent inversion.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.PolygonCubicSections
open PolygonPowerNodeEndpoints
variable (K : Type u) [Field K] (n : ℕ) (a : Fin n → Kˣ)
  (hn₂ : 2 ≤ n) (i : Fin n)

include hn₂ in
/-- Split-node successor components are distinct, including for n = 2. -/
lemma split_successor_ne : finRotate n i ≠ i := by
  let : NeZero n := ⟨by omega⟩
  rw [finRotate_apply]
  intro he
  have h1 : (1 : Fin n) = 0 := add_left_cancel (he.trans (add_zero i).symm)
  have hv := congrArg Fin.val h1
  simp only [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
  omega

include hn₂ in
/-- The predecessor is also distinct from the given component. -/
lemma split_predecessor_ne : (finRotate n).symm i ≠ i := by
  intro he
  have hh := congrArg (finRotate n) he
  rw [Equiv.apply_symm_apply] at hh
  exact split_successor_ne n hn₂ i hh.symm

include hn₂ in
/-- The node numerator on its zero branch is T⁻¹. -/
lemma split_numerator_left_node :
    interpolationLaurent K n a i i 0 = LaurentPolynomial.T (-1) := by
  simp only [interpolationLaurent, cubicDelta, split_predecessor_ne n hn₂ i]
  simp

include hn₂ in
/-- The same node numerator on the successor branch includes its matching weight. -/
lemma split_numerator_right_node :
    interpolationLaurent K n a (finRotate n i) i 0 =
      LaurentPolynomial.C (weight K n a 3 (finRotate n i)) * LaurentPolynomial.T 2 := by
  simp only [interpolationLaurent, cubicDelta, split_successor_ne n hn₂ i,
    Equiv.symm_apply_apply]
  simp

/-- A branch-linear numerator is one on its own component. -/
lemma interpolationLaurent_linear : interpolationLaurent K n a i i 1 = 1 := by
  simp [interpolationLaurent, cubicDelta]

/-- A branch-quadratic numerator is T on its own component. -/
lemma interpolationLaurent_quadratic :
    interpolationLaurent K n a i i 2 = LaurentPolynomial.T 1 := by
  simp [interpolationLaurent, cubicDelta]

/-- Interior coefficients vanish on every different component. -/
lemma interpolationLaurent_interior_other (j : Fin n) (hji : j ≠ i)
    (k : Fin 3) (hk : k ≠ 0) : interpolationLaurent K n a j i k = 0 := by
  simp [interpolationLaurent, cubicDelta, hji, Ne.symm hk]

include hn₂ in
/-- The zero-branch linear coordinate recovers the first branch generator. -/
lemma split_left_numerator_generator :
    LaurentPolynomial.T 1 * interpolationLaurent K n a i i 0 =
      interpolationLaurent K n a i i 1 := by
  rw [split_numerator_left_node K n a hn₂ i, interpolationLaurent_linear]
  rw [← LaurentPolynomial.T_add]
  rfl

include hn₂ in
/-- Inversion on the successor converts its quadratic numerator to its branch generator. -/
lemma split_right_numerator_generator :
    LaurentPolynomial.T 1 *
        LaurentPolynomial.invert (interpolationLaurent K n a (finRotate n i) i 0) =
      LaurentPolynomial.C (weight K n a 3 (finRotate n i)) *
        LaurentPolynomial.invert
          (interpolationLaurent K n a (finRotate n i) (finRotate n i) 2) := by
  rw [split_numerator_right_node K n a hn₂ i, interpolationLaurent_quadratic]
  simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  rw [mul_left_comm, ← LaurentPolynomial.T_add]
  rfl

end FLT.Mazur.PolygonCubicSections
