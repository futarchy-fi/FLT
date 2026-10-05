/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOverlapDiagonal
public import FLT.Mazur.AffinePullbackHomExt
public import FLT.Mazur.AffineReverseGeometricOverlap

/-!
# Recovering the geometric diagonal from tensor contraction

Equality on unit sections detects the actual diagonal pullback equation.
Thus the tensor diagonal law is equivalent to the sheaf diagonal law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineOverlapDiagonal
open AffineOverlapTensor AffineOverlapPullback SchemeModulePullbackUnits
open AffineGeometricOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem contract_other {R S N : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] (s : S) (x : S ⊗[R] N) :
    TensorProduct.lift (Algebra.lsmul R R N (A := S)).toLinearMap
      ((Algebra.lsmul R R N s).lTensor S x) =
    s • TensorProduct.lift (Algebra.lsmul R R N (A := S)).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul t n =>
    simp only [LinearMap.lTensor_tmul, Algebra.lsmul_coe, lift.tmul]
    exact smul_comm t s n
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
local instance (i : S →+* S ⊗[R] S) :
    ((pullback (Spec.map (CommRingCat.ofHom i))).obj M).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback (CommRingCat.ofHom i) M
variable (e : Overlap R S M)

/-- Equality of diagonal evaluation on sections implies the geometric diagonal equation. -/
theorem diagonalCompatible_of_evaluate
    (h : ∀ x, evaluate R S M (right R S) (diagonal_second R S)
      (moduleSpecΓFunctor.map e.hom x) =
        evaluate R S M (left R S) (diagonal_first R S) x) :
    DiagonalCompatible R S M e := by
  apply AffinePullbackHomExt.hom_ext (CommRingCat.ofHom (diagonalRing R S))
    ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M) M
  intro x
  have hn := congrArg (fun k ↦ k.app ⊤ x)
    ((pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (diagonalRing R S)))).unit.naturality e.hom)
  exact (congrArg (fun y ↦ (retractIso _ _ (diagonal_second R S) M).hom.app ⊤ y)
    hn.symm).trans (h x)

set_option maxRecDepth 2048 in
/-- Tensor contraction detects the actual diagonal identity. -/
theorem diagonalCompatible_of_tensor
    (h : ∀ n : coefficients S M,
      TensorProduct.lift (Algebra.lsmul R R (coefficients S M) (A := S)).toLinearMap
        (tensorEquiv R S M e (n ⊗ₜ[R] (1 : S))) = n) :
    DiagonalCompatible R S M e := by
  apply diagonalCompatible_of_evaluate R S M e
  intro x
  obtain ⟨y, rfl⟩ := (firstSections R S M).surjective x
  rw [← tensorEquiv_sections, evaluate_second]
  induction y using TensorProduct.inductionOn with
  | tmul n s =>
    rw [evaluate_first_tmul]
    have hs := tensorEquiv_other_smul R S M e n s 1
    rw [mul_one] at hs
    rw [hs, contract_other, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor and geometric diagonal equations are equivalent. -/
theorem diagonalCompatible_iff_tensor : DiagonalCompatible R S M e ↔
    ∀ n : coefficients S M,
      TensorProduct.lift (Algebra.lsmul R R (coefficients S M) (A := S)).toLinearMap
        (tensorEquiv R S M e (n ⊗ₜ[R] (1 : S))) = n :=
  ⟨fun h ↦ tensorEquiv_diagonal R S M e h, diagonalCompatible_of_tensor R S M e⟩

end FLT.Mazur.AffineOverlapDiagonal
