/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialLineBoundary
public import FLT.Mazur.WeierstrassModificationXResidueNamedGenerators
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureCompatibility

/-!
# Original initial conic punctures agree with the first retained lines

The identities hold on the entire initial tensor algebra. They preserve the
original zero constant coefficient by proof and both signed reciprocal scales.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "t₀" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "v₀" => WeierstrassModificationX.v W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "A" => K ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "Q" => Localization.Away ((1 : K) ⊗ₜ[R] t₀)
local notation "E" => residueFiberEquiv D start hstart (by omega)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "P₁" => conicPuncturedFirst (W.map (residue R)) c hc
local notation "P₂" => conicPuncturedSecond (W.map (residue R)) c hc
local notation "L₁" => initialLineBoundaryMap hπ data D h1 hstart hk 0 (by simp) (tangent)⁻¹
local notation "L₂" => initialLineBoundaryMap hπ data D h1 hstart hk (-a) (by simp) (-tangent)⁻¹

/-- Every original initial tensor function has the first signed reciprocal restriction. -/
theorem initialConicFirstLine_algebra :
    (L₁).comp (Algebra.algHom K A Q) =
      (P₁).comp ((fiberConicMap a c).comp (E).toAlgHom) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassModificationX.hom_ext
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (initialLineBoundaryMap_t hπ data D h1 hstart hk 0 (by simp) (tangent)⁻¹).trans ?_
    rw [inv_inv, WeierstrassDilatation.residueTangentUnit_val]
    change _ = P₁ (fiberConicMap a c (E ((1 : K) ⊗ₜ[R] t₀)))
    erw [residueFiberEquiv_t D start hstart (by omega)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)]
    rw [fiberConicMap_t]
    exact (conicEvaluation_t ..).symm
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (initialLineBoundaryMap_v hπ data D h1 hstart hk 0 (by simp) (tangent)⁻¹).trans ?_
    rw [map_zero]
    change _ = P₁ (fiberConicMap a c (E ((1 : K) ⊗ₜ[R] v₀)))
    erw [residueFiberEquiv_v D start hstart (by omega)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)]
    rw [fiberConicMap_v]
    exact (conicEvaluation_v ..).symm

/-- The opposite puncture keeps its original negative scale and tangent root. -/
theorem initialConicSecondLine_algebra :
    (L₂).comp (Algebra.algHom K A Q) =
      (P₂).comp ((fiberConicMap a c).comp (E).toAlgHom) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassModificationX.hom_ext
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (initialLineBoundaryMap_t hπ data D h1 hstart hk (-a)
      (by simp) (-tangent)⁻¹).trans ?_
    rw [inv_inv, Units.val_neg, WeierstrassDilatation.residueTangentUnit_val, map_neg]
    change _ = P₂ (fiberConicMap a c (E ((1 : K) ⊗ₜ[R] t₀)))
    erw [residueFiberEquiv_t D start hstart (by omega)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)]
    rw [fiberConicMap_t]
    exact (conicEvaluation_t ..).symm
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (initialLineBoundaryMap_v hπ data D h1 hstart hk (-a)
      (by simp) (-tangent)⁻¹).trans ?_
    rw [map_neg]
    change _ = P₂ (fiberConicMap a c (E ((1 : K) ⊗ₜ[R] v₀)))
    erw [residueFiberEquiv_v D start hstart (by omega)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)]
    rw [fiberConicMap_v]
    exact (conicEvaluation_v ..).symm

end FLT.Mazur.WeierstrassDividedDepth
