/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatCoverPointOverlap
public import FLT.GroupScheme.FlatCoverKernelDifferential
public import FLT.GroupScheme.PointDifferenceCotangentEvaluation

/-! # The actual local-point discrepancy on triple overlaps -/

@[expose] public noncomputable section
open scoped TensorProduct
open ThreeAdicPlan.PDivisibleSystem
namespace HopfAlgebra
variable {R A B C D : Type} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [HopfAlgebra R A] [Algebra R B]
  [Algebra B C] [Algebra R C] [IsScalarTower R B C]
  [Algebra B D] [Algebra R D] [IsScalarTower R B D]

/-- The group discrepancy formed from the two actual pullbacks. -/
def coverPointDiscrepancy (y : A →ₐ[R] D) : A →ₐ[R] D ⊗[B] D :=
  pointDifference
    (((Algebra.TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] D).restrictScalars R).comp y)
    (((Algebra.TensorProduct.includeRight : D →ₐ[B] D ⊗[B] D).restrictScalars R).comp y)

/-- The triple-overlap identity holds on the actual coordinates, after subtracting the counit. -/
theorem coverPointDiscrepancy_cocycle
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥)
    (x : A →ₐ[R] C) (y : A →ₐ[R] D)
    (hy : (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
      (Algebra.TensorProduct.includeRight.restrictScalars R).comp x) (a : A) :
    Algebra.overlapCoface₀ B D (coverPointDiscrepancy (B := B) y a) -
      Algebra.overlapCoface₁ B D (coverPointDiscrepancy (B := B) y a) +
      Algebra.overlapCoface₂ B D (coverPointDiscrepancy (B := B) y a) =
        algebraMap R (D ⊗[B] (D ⊗[B] D)) (Bialgebra.counitAlgHom R A a) := by
  let l : D →ₐ[B] D ⊗[B] D := Algebra.TensorProduct.includeLeft
  let r : D →ₐ[B] D ⊗[B] D := Algebra.TensorProduct.includeRight
  let b₁ : D →ₐ[B] D ⊗[B] (D ⊗[B] D) := Algebra.TensorProduct.includeLeft
  let b₂ := (Algebra.overlapCoface₀ B D).comp l
  let b₃ := (Algebra.overlapCoface₀ B D).comp r
  let f := (b₁.restrictScalars R).comp y
  let g := (b₂.restrictScalars R).comp y
  let h := (b₃.restrictScalars R).comp y
  let q := coverPointReduction (R := R) (B := B) (C := C) (D := D ⊗[B] (D ⊗[B] D))
  have hfg : q.comp f = q.comp g :=
    (Algebra.cover_point_reduction_postcomp b₁ x y hy).trans
      (Algebra.cover_point_reduction_postcomp b₂ x y hy).symm
  have hgh : q.comp g = q.comp h :=
    (Algebra.cover_point_reduction_postcomp b₂ x y hy).trans
      (Algebra.cover_point_reduction_postcomp b₃ x y hy).symm
  have he := congrArg (fun t ↦ (t.val a : D ⊗[B] (D ⊗[B] D)))
    (pointDifferenceTangent_cocycle q
      (Algebra.squareZero_coverReduction B C _ hq hJ) f g h hfg hgh)
  change pointDifference f h a - algebraMap R _ (Bialgebra.counitAlgHom R A a) =
    (pointDifference f g a - algebraMap R _ (Bialgebra.counitAlgHom R A a)) +
    (pointDifference g h a - algebraMap R _ (Bialgebra.counitAlgHom R A a)) at he
  have hc₀ : ((Algebra.overlapCoface₀ B D).restrictScalars R).comp
      (coverPointDiscrepancy (B := B) y) = pointDifference g h :=
    pointDifference_postcomp _ _ _
  have hc₁ : ((Algebra.overlapCoface₁ B D).restrictScalars R).comp
      (coverPointDiscrepancy (B := B) y) = pointDifference f h := by
    rw [coverPointDiscrepancy, pointDifference_postcomp]
    congr 1
  have hc₂ : ((Algebra.overlapCoface₂ B D).restrictScalars R).comp
      (coverPointDiscrepancy (B := B) y) = pointDifference f g := by
    rw [coverPointDiscrepancy, pointDifference_postcomp]
    congr 1
  have h₀ := AlgHom.congr_fun hc₀ a
  have h₁ := AlgHom.congr_fun hc₁ a
  have h₂ := AlgHom.congr_fun hc₂ a
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h₀ h₁ h₂
  rw [h₀, h₁, h₂]
  linear_combination -he

end HopfAlgebra
