/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalTopCoefficient
public import FLT.Mazur.PolygonLaurentRestrictionKernel

/-!
# Canonical top coefficients in both Laurent variables

The top smoothing coefficient is an actual double Laurent polynomial over
the reduced base. It reconstructs any element in the adjacent restriction
kernel and detects its vanishing without any arbitrary choice of a factor.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
variable (R : Type*) [CommRing R] (m : ℕ)

/-- Apply one smoothing coefficient functional to every Laurent coefficient. -/
def laurentStageCoeff (j : ℕ) : (Ring R m)[T;T⁻¹] →+ R[T;T⁻¹] where
  toFun := AddMonoidAlgebra.map (stageCoeff R m j).toAddMonoidHom
  map_zero' := AddMonoidAlgebra.map_zero _
  map_add' := AddMonoidAlgebra.map_add _

/-- Extract a smoothing coefficient while retaining both Laurent coordinates. -/
def doubleLaurentStageCoeff (j : ℕ) : (Ring R m)[T;T⁻¹][T;T⁻¹] →+ R[T;T⁻¹][T;T⁻¹] where
  toFun := AddMonoidAlgebra.map (laurentStageCoeff R m j)
  map_zero' := AddMonoidAlgebra.map_zero _
  map_add' := AddMonoidAlgebra.map_add _

/-- The extracted polynomial has precisely the canonical coefficient at each Laurent monomial. -/
theorem doubleLaurentStageCoeff_coeff (j : ℕ) (p : (Ring R m)[T;T⁻¹][T;T⁻¹])
    (a b : ℤ) :
    ((doubleLaurentStageCoeff R m j p).coeff a).coeff b =
      stageCoeff R m j ((p.coeff a).coeff b) := rfl

/-- Multiplication by a double constant multiplies each of the original coefficients. -/
theorem doubleLaurent_constant_mul_coeff (r : R) (p : R[T;T⁻¹][T;T⁻¹]) (a b : ℤ) :
    ((C (C r) * p).coeff a).coeff b = r * (p.coeff a).coeff b := by
  simp only [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

/-- The top parameter power embeds a reduced Laurent polynomial into the top stage layer. -/
theorem laurent_top_lift_eq_zero_iff (p : R[T;T⁻¹]) :
    C (parameter R m ^ m) * coeffMap (algebraMap R (Ring R m)) p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    ext a
    have he := congrArg (fun f ↦ stageCoeff R m m (f.coeff a)) hp
    rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      coeffMap_coeff, stageCoeff_top_mul] at he
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero] using he
  · rintro rfl
    rw [map_zero, mul_zero]

/-- The top Laurent polynomial reconstructs the full adjacent-kernel element. -/
theorem doubleLaurent_restriction_kernel_top (p : (Ring R (m + 1))[T;T⁻¹][T;T⁻¹])
    (hp : coeffMap (coeffMap (restriction R m).toRingHom) p = 0) :
    p = C (C (parameter R (m + 1))) ^ (m + 1) *
      coeffMap (coeffMap (algebraMap R (Ring R (m + 1))))
        (doubleLaurentStageCoeff R (m + 1) (m + 1) p) := by
  rw [← map_pow, ← map_pow]
  ext a b
  rw [doubleLaurent_constant_mul_coeff, coeffMap_coeff, coeffMap_coeff,
    doubleLaurentStageCoeff_coeff]
  apply restriction_kernel_top
  change (restriction R m).toRingHom ((p.coeff a).coeff b) = 0
  have he := congrArg (fun f ↦ (f.coeff a).coeff b) hp
  simpa only [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he

/-- The top polynomial detects exact vanishing throughout the adjacent Laurent kernel. -/
theorem doubleLaurent_restriction_kernel_eq_zero_iff
    (p : (Ring R (m + 1))[T;T⁻¹][T;T⁻¹])
    (hp : coeffMap (coeffMap (restriction R m).toRingHom) p = 0) :
    p = 0 ↔ doubleLaurentStageCoeff R (m + 1) (m + 1) p = 0 := by
  constructor
  · rintro rfl
    exact map_zero _
  · intro hc
    rw [doubleLaurent_restriction_kernel_top R m p hp, hc, map_zero, mul_zero]

end FLT.Mazur.PolygonInfinitesimalStages
