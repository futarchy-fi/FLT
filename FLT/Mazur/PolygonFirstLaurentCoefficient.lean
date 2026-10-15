/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodePrincipalParts
public import FLT.Mazur.PolygonLaurentTopCoefficient

/-!
# Exact coefficients of arbitrary first-order Laurent defects

The canonical first coefficient is inverse to parameter weighting on the
entire reduction kernel. Consequently principal parts can be computed from
a full nilpotent branch pair without choosing any factor or node lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
open LaurentNodePrincipalParts
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "L" => (S)[T;T⁻¹]

/-- The canonical first coefficient recovers every weighted Laurent polynomial. -/
theorem firstLaurentParameterLift_coefficient (p : R[T;T⁻¹]) :
    laurentStageCoeff R 1 1 (firstLaurentParameterLift R p) = p := by
  ext d
  change stageCoeff R 1 1 ((firstLaurentParameterLift R p).coeff d) = p.coeff d
  rw [firstLaurentParameterLift, ← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
    smul_eq_mul, coeffMap_coeff, ← pow_one (e), stageCoeff_top_mul]
  exact (reduction R 1).commutes _

/-- A scalar with zero reduction is reconstructed by its canonical first coefficient. -/
theorem firstScalar_reconstruct (s : S) (hs : reduction R 1 s = 0) :
    (e) * algebraMap R (S) (stageCoeff R 1 1 s) = s := by
  obtain ⟨b, hb⟩ := (reduction_eq_zero_iff R 1 s).mp hs
  rw [← hb, ← pow_one (e), stageCoeff_top_mul]
  exact (parameter_top_mul_reduction R 1 b).symm

/-- Every full Laurent reduction-kernel element is recovered without choosing a factor. -/
theorem firstLaurent_reconstruct (p : L)
    (hp : coeffMap (reduction R 1).toRingHom p = 0) :
    firstLaurentParameterLift R (laurentStageCoeff R 1 1 p) = p := by
  ext d
  rw [firstLaurentParameterLift, ← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
    smul_eq_mul, coeffMap_coeff]
  change (e) * algebraMap R (S) (stageCoeff R 1 1 (p.coeff d)) = p.coeff d
  apply firstScalar_reconstruct
  have he := congrArg (fun q : R[T;T⁻¹] ↦ q.coeff d) hp
  simp only [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at he
  exact (show reduction R 1 (p.coeff d) =
    (reduction R 1).toRingHom (p.coeff d) from rfl).trans he

/-- Extract both full parameter coefficients by an actual additive map. -/
def firstNodePairCoefficient : ((L) × (L)) →+ (R[T;T⁻¹] × R[T;T⁻¹]) :=
  (laurentStageCoeff R 1 1).prodMap (laurentStageCoeff R 1 1)

/-- Coefficient extraction is a left inverse to weighting on both complete branches. -/
theorem firstNodePairCoefficient_weighted (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodePairCoefficient R (firstNodeParameterPair R p) = p :=
  Prod.ext (firstLaurentParameterLift_coefficient R p.1)
    (firstLaurentParameterLift_coefficient R p.2)

/-- Parameter annihilation is enough to reconstruct a full branch pair from its coefficients. -/
theorem firstNodePairCoefficient_reconstruct (p : (L) × (L)) (hp : (e) • p = 0) :
    firstNodeParameterPair R (firstNodePairCoefficient R p) = p := by
  apply Prod.ext
  · apply firstLaurent_reconstruct
    apply (firstLaurent_parameter_eq_zero_iff R p.1).mp
    exact (smul_eq_C_mul _ _).symm.trans (congrArg Prod.fst hp)
  · apply firstLaurent_reconstruct
    apply (firstLaurent_parameter_eq_zero_iff R p.2).mp
    exact (smul_eq_C_mul _ _).symm.trans (congrArg Prod.snd hp)

/-- Explicit principal parts detect descent of any parameter-annihilated full branch pair. -/
theorem firstNodePair_mem_iff_principalParts (p : (L) × (L)) (hp : (e) • p = 0) :
    p ∈ firstNodeBranchSubalgebra R ↔ principalParts (firstNodePairCoefficient R p) = 0 := by
  conv_lhs => rw [← firstNodePairCoefficient_reconstruct R p hp]
  exact firstNodeParameterPair_mem_iff R _

end FLT.Mazur.PolygonInfinitesimalStages
