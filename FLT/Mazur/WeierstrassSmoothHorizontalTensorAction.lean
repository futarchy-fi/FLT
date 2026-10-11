/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalActionAlgebra
public import FLT.Mazur.WeierstrassModificationXResidueTensorFunctions

/-!
# The constructed action on the original horizontal tensor chart

Extend the actual fraction-algebra action over the residue field after the
proved original equation-chart equivalence. Both maps factor through the
original conic in the complete tensor chart.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => WeierstrassModificationX.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "E" => horizontalReesChartEquiv W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
local notation "F" => residueFiberEquiv D k hk0 (Nat.le_of_lt hk)
  d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "N" => residueNormalMap D k hk0 (Nat.le_of_lt hk)
  d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "a" => residue R W.a₁
local notation "c" => residue R d.b6
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D k hk d.b6 d.factor6)
local notation "P₁" => conicPuncturedFirst (W.map (residue R)) c hc
local notation "P₂" => conicPuncturedSecond (W.map (residue R)) c hc
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D

/-- The first constructed residue action on the actual tensor equation chart. -/
def smoothHorizontalFirstTensorAction : K ⊗[R] A →ₐ[K] C :=
  AlgHom.liftEquiv R K A C
    ((smoothHorizontalFirstAction D d hk0 hk hπ).comp (E).toAlgHom)

/-- The opposite constructed residue action on the same original tensor chart. -/
def smoothHorizontalSecondTensorAction : K ⊗[R] A →ₐ[K] C :=
  AlgHom.liftEquiv R K A C
    ((smoothHorizontalSecondAction D d hk0 hk hπ).comp (E).toAlgHom)

/-- The first tensor action retains the actual original conic and its positive character. -/
theorem smoothHorizontalFirstTensorAction_conic :
    smoothHorizontalFirstTensorAction D d hk0 hk hπ =
      (smoothHorizontalLaurentEvaluation D (τ * z)).comp
        ((P₁).comp ((fiberConicMap a c).comp (F).toAlgHom)) := by
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro f
  simp only [smoothHorizontalFirstTensorAction, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  rw [smoothHorizontalFirstAction_eq]
  change smoothHorizontalLaurentEvaluation D (τ * z)
    (P₁ (fiberConicMap a c (N ((E).symm (E f))))) =
      smoothHorizontalLaurentEvaluation D (τ * z)
        (P₁ (fiberConicMap a c (F ((1 : K) ⊗ₜ[R] f))))
  rw [AlgEquiv.symm_apply_apply, residueFiberEquiv_tmul, one_smul]

/-- The opposite tensor action retains the original conic with the inverse character. -/
theorem smoothHorizontalSecondTensorAction_conic :
    smoothHorizontalSecondTensorAction D d hk0 hk hπ =
      (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).comp
        ((P₂).comp ((fiberConicMap a c).comp (F).toAlgHom)) := by
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro f
  simp only [smoothHorizontalSecondTensorAction, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  rw [smoothHorizontalSecondAction_eq]
  change smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)
    (P₂ (fiberConicMap a c (N ((E).symm (E f))))) =
      smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)
        (P₂ (fiberConicMap a c (F ((1 : K) ⊗ₜ[R] f))))
  rw [AlgEquiv.symm_apply_apply, residueFiberEquiv_tmul, one_smul]

end FLT.Mazur.WeierstrassIntegralChart
