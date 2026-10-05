/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TensorScalarComparison

/-!
# Overlap cocycles induced by effective scalar recovery

Each coefficient embedding into an overlap ring pulls back the constructed
scalar recovery. Comparing two such trivializations gives the descent map;
on a triple overlap its cocycle identity follows by cancelling the middle
trivialization.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S T A H : Type u} [CommRing R] [CommRing S] [CommRing T]
  [CommRing A] [CommRing H] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R H]
  (e : S ⊗[R] A ≃ₐ[S] S ⊗[R] H)

/-- Pull back the effective recovery along a specified coefficient embedding. -/
def recoveryAlong (α : S →ₐ[R] T) : T ⊗[R] A ≃ₐ[T] T ⊗[R] H := by
  letI := α.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' α.comp_algebraMap.symm
  exact (Algebra.TensorProduct.cancelBaseChange R S T T A).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) e).trans
      (Algebra.TensorProduct.cancelBaseChange R S T T H))

/-- The overlap transition compares the two actual pullbacks of scalar recovery. -/
def recoveryOverlap (α β : S →ₐ[R] T) : T ⊗[R] H ≃ₐ[T] T ⊗[R] H :=
  (recoveryAlong e α).symm.trans (recoveryAlong e β)

/-- Identity overlap transitions are the identity. -/
theorem recoveryOverlap_refl (α : S →ₐ[R] T) :
    recoveryOverlap e α α = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  exact (recoveryAlong e α).apply_symm_apply x

/-- The two-step transition on a triple overlap equals the direct transition. -/
theorem recoveryOverlap_cocycle (α β γ : S →ₐ[R] T) :
    (recoveryOverlap e α β).trans (recoveryOverlap e β γ) = recoveryOverlap e α γ := by
  apply AlgEquiv.ext
  intro x
  simp only [recoveryOverlap, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]


/-- The three embeddings of the splitting ring into its left-associated triple overlap. -/
def tripleOverlapLeft : S →ₐ[R] (S ⊗[R] S) ⊗[R] S :=
  Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft

/-- The middle embedding into the triple overlap. -/
def tripleOverlapMiddle : S →ₐ[R] (S ⊗[R] S) ⊗[R] S :=
  Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight

/-- The last embedding into the triple overlap. -/
def tripleOverlapRight : S →ₐ[R] (S ⊗[R] S) ⊗[R] S :=
  Algebra.TensorProduct.includeRight

/-- The descent transitions satisfy the cocycle on the actual threefold tensor overlap. -/
theorem recoveryOverlap_triple :
    (recoveryOverlap e tripleOverlapLeft tripleOverlapMiddle).trans
      (recoveryOverlap e tripleOverlapMiddle tripleOverlapRight) =
        recoveryOverlap e tripleOverlapLeft tripleOverlapRight :=
  recoveryOverlap_cocycle e _ _ _

end SemilinearDescent
