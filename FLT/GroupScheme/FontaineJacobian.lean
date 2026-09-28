/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineQuotientValuation
public import FLT.GroupScheme.FiniteFlatDifferentials
public import FLT.Mathlib.RingTheory.GeneratorsDifferentialRelations
public import FLT.Mathlib.Analysis.Normed.Field.ScalarPerturbation

/-!
# Jacobian control without a monogenic presentation

For any finite generating family of a killed-by-three model and any approximate
point of precision greater than one, select relations whose Jacobian is a
small perturbation of three times the identity. The resulting Jacobian is
invertible and its inverse loses exactly one unit of valuation precision.

The selected relations are not asserted to generate the entire relation ideal;
this statement alone does not construct an integral point of the model.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- Every approximate point of an arbitrary killed-by-three model admits
integral coordinate lifts and selected relations with inverse Jacobian norm
exactly three. No power basis or prescribed relation degrees are required. -/
theorem FF.exists_approximate_jacobian_equiv {ι : Type*} [Fintype ι]
    (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (P : Algebra.Generators ℤ_[3] M.CoordinateRing ι)
    {m : ℚ} (hm : 1 < m)
    (u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) :
    let := spectralNorm.nontriviallyNormedField ℚ_[3] E
    ∃ (x : ι → ThreeAdicIntegers E) (f : ι → MvPolynomial ι ℤ_[3])
      (e : (ι → E) ≃ₗ[E] (ι → E)),
      (∀ i, Ideal.Quotient.mk (threeAdicValuationIdeal E m) (x i) = u (P.val i)) ∧
      (∀ i, f i ∈ P.ker) ∧
      (∀ i, aeval x (f i) ∈ threeAdicValuationIdeal E m) ∧
      (∀ v i, e v i = ∑ j, aeval (fun k ↦ (x k : E)) (pderiv j (f i)) * v j) ∧
      ∀ w, ‖e.symm w‖ = 3 * ‖w‖ := by
  classical
  let := spectralNorm.nontriviallyNormedField ℚ_[3] E
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (u (P.val i))
  obtain ⟨f, hf, hval, hder⟩ := P.exists_relations_approximate_jacobian 3
    (M.three_smul_kaehlerDifferential_eq_zero hM) (threeAdicValuationIdeal E m) u x hx
  let A : Matrix ι ι E := fun i j ↦ aeval (fun k ↦ (x k : E)) (pderiv j (f i))
  have hA (i j : ι) : ‖A i j - (if i = j then (3 : E) else 0)‖ ≤
      (3 : ℝ) ^ (-(m : ℝ)) := by
    have hh := hder i j
    change ‖(ThreeAdicIntegers E).val (aeval x (pderiv j (f i))) -
      (ThreeAdicIntegers E).val
        (if i = j then algebraMap ℤ_[3] (ThreeAdicIntegers E) 3 else 0)‖ ≤ _ at hh
    have he : (ThreeAdicIntegers E).val (aeval x (pderiv j (f i))) = A i j :=
      MvPolynomial.comp_aeval_apply x (ThreeAdicIntegers E).val _
    simpa only [map_sub, apply_ite, map_zero, map_ofNat, he] using hh
  have hε : (3 : ℝ) ^ (-(m : ℝ)) < ‖(3 : E)‖ := by
    rw [show ‖(3 : E)‖ = (3 : ℝ)⁻¹ from spectralNorm_three E, ← Real.rpow_neg_one]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    exact_mod_cast neg_lt_neg hm
  obtain ⟨e, he, hn⟩ := Matrix.exists_linearEquiv_of_entrywise_scalar_perturbation
    (isNonarchimedean_spectralNorm (K := ℚ_[3]) (L := E)) A 3 (by positivity) hε hA
  refine ⟨x, f, e, hx, hf, hval, fun v i ↦ congrFun (he v) i, fun w ↦ ?_⟩
  rw [hn, show ‖(3 : E)‖ = (3 : ℝ)⁻¹ from spectralNorm_three E]
  ring

end ThreeAdicPlan
