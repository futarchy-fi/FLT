/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentBranches

/-!
# Arithmetic orientations of the original initial Laurent slopes

The small slope is nilpotent and the opposite slope differs from minus a₁
by a nilpotent element, including the original b₃/T correction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "B" => R[T;T⁻¹]
local notation "K" => laurentArithmeticIdeal I
local notation "v" label => laurentBranchSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 label
local notation "a" => algebraMap R B W.a₁

/-- The original small branch slope lies in the nilpotent coefficient ideal. -/
theorem laurentBranchSlope_small_mem : (v false) ∈ K :=
  nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The opposite branch retains its original translated tangent modulo the coefficient ideal. -/
theorem laurentBranchSlope_opposite_add_mem : (v true) + a ∈ K := by
  have hb : algebraMap R B b3 * LaurentPolynomial.T (-1) ∈ K :=
    (K).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  have hv := laurentBranchSlope_small_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
  change -(v false) - (a + algebraMap R B b3 * LaurentPolynomial.T (-1)) + a ∈ K
  convert (K).neg_mem ((K).add_mem hb hv) using 1
  ring

/-- The small branch's opposite tangent is invertible on the entire Laurent scheme. -/
theorem laurentBranchSlope_small_add_unit : IsUnit ((v false) + a) :=
  (NilpotentQuadraticRoot.element_nilpotent K (laurentArithmeticIdeal_nilpotent I hI)
    (laurentBranchSlope_small_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)).isUnit_add_right_of_commute
      (ha.map (algebraMap R B)) (mul_comm _ _)

/-- The full opposite Laurent slope is invertible, with all nilpotent corrections retained. -/
theorem laurentBranchSlope_opposite_unit : IsUnit ((v true)) := by
  have hn := NilpotentQuadraticRoot.element_nilpotent K (laurentArithmeticIdeal_nilpotent I hI)
    (laurentBranchSlope_opposite_add_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  have hu := hn.isUnit_add_right_of_commute (ha.map (algebraMap R B)).neg (mul_comm _ _)
  simpa only [add_neg_cancel_right] using hu

end FLT.Mazur.WeierstrassModificationX
