/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointMarkedLaurentNumerators
public import FLT.Mazur.PolygonSmoothingLaurentMonomials

/-!
# Finite Laurent bounds for the actual retained numerators

At stage m the outgoing numerator of a degree-d global section has support
in [-m,d+m]. The lower coefficients remain the original ones; the bound
uses the incoming chart and the full regular marking transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "t" => parameter K m
local notation "L" => originalStageSinglePointLine K n h m i
local notation "N" d:max s:max => leftLaurentMap (t)
  (completePointStageChartNumerator K n h m i i d s)

/-- The outgoing numerator has no terms below the original nilpotence bound. -/
theorem completePointStageNumerator_coefficient_below (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) (hk : k < -(m : ℤ)) :
    (N d s).coeff k = 0 :=
  leftLaurentMap_coefficient_below (t) m (parameter_pow K m) _ k hk

/-- The incoming chart bounds the upper tail before any parameter reduction. -/
theorem completePointStageNumerator_coefficient_above (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (k : ℤ) (hk : (d : ℤ) + m < k) :
    (N d s).coeff k = 0 := by
  have he := completePointStageNumerator_marked_coefficient K n h m i d s (k - d)
  rw [sub_add_cancel] at he
  have hz := precedingLaurentMap_coefficient_above (t) m (parameter_pow K m)
    (completePointStageChartNumerator K n h m i ((finRotate n).symm i) d s)
    (k - d) (by omega)
  rw [hz] at he
  apply (((isUnit_one : IsUnit (1 : Ring K m)).neg).pow d).isRegular.left
  simpa only [mul_zero] using he.symm

/-- All coefficients of the original degree-d numerator lie in this finite interval. -/
theorem completePointStageNumerator_support (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (N d s).coeff.support ⊆ Finset.Icc (-(m : ℤ)) ((d : ℤ) + m) := by
  intro k hk
  have hn := Finsupp.mem_support_iff.mp hk
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hb
    exact hn (completePointStageNumerator_coefficient_below K n h m i d s k (by omega))
  · by_contra hb
    exact hn (completePointStageNumerator_coefficient_above K n h m i d s k (by omega))

/-- The actual numerator is the finite Laurent sum of its own retained coefficients. -/
theorem completePointStageNumerator_expansion (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (N d s) = ∑ k ∈ Finset.Icc (-(m : ℤ)) ((d : ℤ) + m),
      LaurentPolynomial.C ((N d s).coeff k) * LaurentPolynomial.T k := by
  have hs := completePointStageNumerator_support K n h m i d s
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (N d s)]
  change (N d s).coeff.sum AddMonoidAlgebra.single = _
  rw [Finsupp.sum_of_support_subset _ hs
    (fun k r ↦ (AddMonoidAlgebra.single k r : (Ring K m)[T;T⁻¹]))
    (by intro k _; exact AddMonoidAlgebra.single_zero k)]
  simp only [LaurentPolynomial.single_eq_C_mul_T]

end FLT.Mazur.PolygonInfinitesimalStages
