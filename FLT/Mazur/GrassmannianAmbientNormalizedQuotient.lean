/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartRepresentation

/-!
# Normalized quotient maps in original ambient coordinates

The matrix evaluation is transported through the actual ambient chart index.
Its kernel is the entire original relation, and its quotient comparison is an
actual linear equivalence. Pure tensors have explicit finite coordinates.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Normalized evaluation in the original ambient module after scalar extension. -/
def ambientNormalizedQuotient (i : AmbientChartIndex R M κ d)
    (c : (κ → A) →ₗ[A] (Fin d → A)) : (A ⊗[R] M) →ₗ[A] (Fin d → A) :=
  (splitChartEvaluation c).comp (ambientChartBaseChange A i).symm.toLinearMap

/-- The actual original chart point defined by a complementary coordinate map. -/
def ambientPointOfCoordinates (i : AmbientChartIndex R M κ d)
    (c : (κ → A) →ₗ[A] (Fin d → A)) :
    AmbientChartPoint (ambientChartBaseChange A i) :=
  ambientChartPointOfSplit _ (splitChartOfCoordinates c)

/-- Its quotient identifies with the selected free module, through the original quotient. -/
def ambientNormalizedQuotientEquiv (i : AmbientChartIndex R M κ d)
    (c : (κ → A) →ₗ[A] (Fin d → A)) :
    ((A ⊗[R] M) ⧸ (ambientPointOfCoordinates i c).val.toSubmodule) ≃ₗ[A] (Fin d → A) :=
  (ambientTransportQuotientEquiv (ambientChartBaseChange A i)
    (splitChartGrassmannian c)).trans (splitChartQuotientEquiv c)

/-- The comparison intertwines the full quotient map with normalized evaluation. -/
theorem ambientNormalizedQuotientEquiv_mkQ (i : AmbientChartIndex R M κ d)
    (c : (κ → A) →ₗ[A] (Fin d → A)) :
    (ambientNormalizedQuotientEquiv i c).toLinearMap.comp
      (ambientPointOfCoordinates i c).val.toSubmodule.mkQ =
        ambientNormalizedQuotient i c := by
  apply LinearMap.ext
  intro x
  change splitChartQuotientEquiv c
    (ambientTransportQuotientEquiv (ambientChartBaseChange A i) (splitChartGrassmannian c)
      (Submodule.Quotient.mk x)) = _
  rw [ambientTransportQuotientEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]
  change splitChartQuotientEquiv c
    (Submodule.Quotient.mk ((ambientChartBaseChange A i).symm x)) = _
  rw [splitChartQuotientEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- Normalized evaluation retains every original ambient relation. -/
theorem ambientNormalizedQuotient_kernel (i : AmbientChartIndex R M κ d)
    (c : (κ → A) →ₗ[A] (Fin d → A)) :
    (ambientNormalizedQuotient i c).ker = (ambientPointOfCoordinates i c).val.toSubmodule := by
  rw [← ambientNormalizedQuotientEquiv_mkQ, LinearEquiv.ker_comp, Submodule.ker_mkQ]

/-- Scalar-extended inverse ambient coordinates on every pure tensor. -/
theorem ambientChartBaseChange_symm_tmul (i : AmbientChartIndex R M κ d) (a : A) (m : M) :
    (ambientChartBaseChange A i).symm (a ⊗ₜ[R] m) =
      ((fun j ↦ algebraMap R A ((i.symm m).1 j) * a),
        fun k ↦ algebraMap R A ((i.symm m).2 k) * a) := by
  change splitAmbientTensorEquiv A κ d ((i.baseChange R A).symm (a ⊗ₜ[R] m)) = _
  rw [← LinearEquiv.baseChange_symm, LinearEquiv.baseChange_tmul,
    splitAmbientTensorEquiv_tmul]

/-- Normalized evaluation on pure tensors is the explicit finite matrix formula. -/
theorem ambientNormalizedQuotient_tmul (i : AmbientChartIndex R M κ d)
    (c : (κ → A) →ₗ[A] (Fin d → A)) (a : A) (m : M) :
    ambientNormalizedQuotient i c (a ⊗ₜ[R] m) =
      (fun j ↦ algebraMap R A ((i.symm m).1 j) * a) +
        c (fun k ↦ algebraMap R A ((i.symm m).2 k) * a) := by
  simp only [ambientNormalizedQuotient, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [ambientChartBaseChange_symm_tmul]
  rfl

end FLT.Mazur.GrassmannianChart
