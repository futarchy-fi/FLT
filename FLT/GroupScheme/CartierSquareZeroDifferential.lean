/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierCotangentTensor
public import FLT.GroupScheme.SquareZeroAugmentationPoints

/-! # The actual square-zero logarithmic derivative of an integral Cartier character -/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual
variable {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- The derivative is linear on the actual augmentation tangents. -/
def testLogDifferential (ψ : CartierDual R A →ₐ[R] S) :
    (Bialgebra.counitAlgHom R A).augmentationTangent (M := S) →ₗ[R] S :=
  (testEvaluation ψ).comp (Bialgebra.counitAlgHom R A).augmentationTangent.subtype

/-- It is contraction against the original cotangent tensor, hence respects its quotient. -/
theorem testLogDifferential_pairing (ψ : CartierDual R A →ₐ[R] S)
    (d : (Bialgebra.counitAlgHom R A).augmentationTangent (M := S)) :
    testLogDifferential ψ d = testDlogPairing ψ
      ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv.symm d) := by
  rw [testDlogPairing_eq, LinearEquiv.apply_symm_apply]
  rfl

/-- Embed the actual square-zero kernel tangent into the test algebra coefficients. -/
def testKernelTangent (q : S →ₐ[R] T) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    (Bialgebra.counitAlgHom R A).augmentationTangent (M := S) := by
  let d := AlgHom.augmentationPointToTangent (Bialgebra.counitAlgHom R A) q hJ f
  refine ⟨((RingHom.ker q).subtype.restrictScalars R).comp d.val, ?_⟩
  intro a b
  exact congrArg Subtype.val (d.property a b)

omit [Module.Finite R A] [Module.Free R A] in
/-- The kernel tangent is computed on the original coordinate representatives. -/
theorem testKernelTangent_apply (q : S →ₐ[R] T) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) (a : A) :
    (testKernelTangent q hJ f).val a =
      f.val a - algebraMap R S (Coalgebra.counit a) := rfl

/-- On a square-zero point the actual character is one plus its logarithmic derivative. -/
theorem testCharacter_squareZero (ψ : CartierDual R A →ₐ[R] S)
    (q : S →ₐ[R] T) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    (testCharacter ψ (WithConv.toConv f.val) : S) - 1 =
      testLogDifferential ψ (testKernelTangent q hJ f) := by
  have he : testEvaluation ψ
      (((Algebra.ofId R S).comp (Bialgebra.counitAlgHom R A)).toLinearMap) = 1 :=
    map_one (testCharacterValue ψ)
  rw [testCharacter_coe, ← he, ← map_sub]
  rfl

/-- The derivative lands in the actual reduction kernel. -/
theorem testLogDifferential_mem_kernel (ψ : CartierDual R A →ₐ[R] S)
    (q : S →ₐ[R] T) (hJ : RingHom.ker q ^ 2 = ⊥)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    testLogDifferential ψ (testKernelTangent q hJ f) ∈ RingHom.ker q := by
  change testEvaluation ψ (testKernelTangent q hJ f).val ∈ RingHom.ker q
  rw [testEvaluation_eq_sum (Module.Free.chooseBasis R A)]
  apply Ideal.sum_mem
  intro i hi
  apply Ideal.mul_mem_right
  exact (AlgHom.augmentationPointToTangent (Bialgebra.counitAlgHom R A) q hJ f).val
    (Module.Free.chooseBasis R A i) |>.property

end HopfAlgebra.CartierDual
