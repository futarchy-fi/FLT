/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineMarkedEndpointSections
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Equal endpoint values for the single marked component

The other components of a polygon carry the trivial single-point line. Their
constant sections require the two endpoints of the marked component to agree.
Here the actual H0 coordinate equivalence computes this condition and its
dimension. Identifying it with the whole polygon normalization kernel is a
separate gluing step.
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry

namespace FLT.Mazur.ProjectiveLinePointLoopMatching

open FCurve ProjectiveLineMarkedHZero

variable (K : Type) [Field K] (a : Kˣ) (m : ℕ)

/-- Infinity minus zero, measured in the original canonical divisor-section frames. -/
def polynomialDifference : degreeLT K (m + 1) →ₗ[K] K where
  toFun p := p.val.coeff m - p.val.coeff 0 / (-(a : K)) ^ m
  map_add' p q := by simp [add_div]; ring
  map_smul' c p := by simp [mul_div_assoc, mul_sub]

/-- A positive pole bound allows arbitrary endpoint discrepancy. -/
theorem polynomialDifference_surjective (hm : 0 < m) :
    Function.Surjective (polynomialDifference K a m) := by
  intro c
  refine ⟨⟨monomial m c, monomial_coe_mem_degreeLT ⟨m, by omega⟩ c⟩, ?_⟩
  simp [polynomialDifference, coeff_monomial, Nat.ne_of_gt hm]

/-- The actual H0 endpoint discrepancy, with no chosen basis of sheaf cohomology. -/
def difference : H0 K a m →ₗ[K] K :=
  (polynomialDifference K a m).comp (polynomialEquiv K a m).toLinearMap

/-- Its kernel consists precisely of sections with the same canonical endpoint scalars. -/
theorem mem_kernel_iff (x : H0 K a m) :
    x ∈ LinearMap.ker (difference K a m) ↔
      ((polynomialEquiv K a m x).val).coeff m =
        ((polynomialEquiv K a m x).val).eval 0 / (-(a : K)) ^ m := by
  simp only [LinearMap.mem_ker, difference, LinearMap.comp_apply,
    LinearEquiv.coe_coe, polynomialDifference, LinearMap.coe_mk, AddHom.coe_mk,
    sub_eq_zero, coeff_zero_eq_eval_zero]

/-- Every discrepancy has an actual global-section cohomology lift. -/
theorem difference_surjective (hm : 0 < m) : Function.Surjective (difference K a m) :=
  (polynomialDifference_surjective K a m hm).comp (polynomialEquiv K a m).surjective

/-- The matching actual H0 space has dimension exactly the positive pole bound. -/
theorem finrank_kernel (hm : 0 < m) :
    Module.finrank K (LinearMap.ker (difference K a m)) = m := by
  let _ := (polynomialEquiv K a m).symm.finiteDimensional
  have he := (difference K a m).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (difference_surjective K a m hm),
    finrank_top, Module.finrank_self, (polynomialEquiv K a m).finrank_eq,
    (degreeLTEquiv K (m + 1)).finrank_eq] at he
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  omega

/-- The first pole bound leaves exactly one matching section dimension. -/
theorem finrank_kernel_one : Module.finrank K (LinearMap.ker (difference K a 1)) = 1 :=
  finrank_kernel K a 1 (by decide)

open ProjectiveLineMarkedSectionTransition ProjectiveLineMarkedCharts
open ProjectiveLineMarkedEndpointSections in
/-- Matching classes have the same scalar at both actual geometric endpoints. -/
theorem matching_endpoints (x : H0 K a m) (hx : x ∈ LinearMap.ker (difference K a m)) :
    ∃ c : K,
      pullGlobal (ProjectiveLine.zero K) (line K a m)
          (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x) =
        (Scheme.ΓSpecIso (.of K)).inv c •
          pullGlobal (ProjectiveLine.zero K) (line K a m)
            (divisorSection ((relativeCartier K a).1.pow m) ⊤) ∧
      pullGlobal (ProjectiveLine.infinity K) (line K a m)
          (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x) =
        (Scheme.ΓSpecIso (.of K)).inv c •
          pullGlobal (ProjectiveLine.infinity K) (line K a m)
            (divisorSection ((relativeCartier K a).1.pow m) ⊤) := by
  refine ⟨((polynomialEquiv K a m x).val).coeff m, ?_, infinity_h0 K a m x⟩
  rw [zero_h0, ← (mem_kernel_iff K a m x).mp hx]

end FLT.Mazur.ProjectiveLinePointLoopMatching
