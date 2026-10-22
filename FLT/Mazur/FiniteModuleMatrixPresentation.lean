/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MatrixCokernelScalarExtension
public import FLT.Mazur.MatrixCokernelFlatCertificate

/-!
# Finite module presentations and their actual scalar extensions

Every finitely presented module has a finite matrix presentation. Its fixed
presentation identifies scalar extension with the coefficient-mapped cokernel,
so flatness can be tested there without changing the original module.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.MatrixCokernel
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Extract a genuine finite matrix presentation from finite presentation of the module. -/
theorem exists_matrix_presentation [Module.FinitePresentation R M] :
    ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) R),
      Nonempty (((Fin m → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R] M) := by
  obtain ⟨m, n, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R M
  refine ⟨m, n, LinearMap.toMatrix' g, ?_⟩
  have hker : LinearMap.range (LinearMap.toMatrix' g).mulVecLin = LinearMap.ker f := by
    rw [show (LinearMap.toMatrix' g).mulVecLin = g from Matrix.toLin'_toMatrix' g]
    exact hg.linearMap_ker_eq.symm
  exact ⟨(Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf)⟩

variable (S : Type*) [CommRing S] [Algebra R S]
  {m n : Type*} [Finite m] [Fintype n]

/-- The original module's presentation induces its scalar recovery comparison. -/
def presentationScalarEquiv (A : Matrix m n R)
    (e : ((m → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R] M) :
    S ⊗[R] M ≃ₗ[S] ((m → S) ⧸ LinearMap.range (A.map (algebraMap R S)).mulVecLin) :=
  (e.symm.baseChange R S _ _).trans (scalarExtensionEquiv S A)

/-- Flatness of actual scalar extension is exactly flatness of the mapped presentation. -/
theorem flat_tensor_iff_matrix (A : Matrix m n R)
    (e : ((m → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R] M) :
    Module.Flat S (S ⊗[R] M) ↔
      Module.Flat S ((m → S) ⧸ LinearMap.range (A.map (algebraMap R S)).mulVecLin) :=
  Module.Flat.equiv_iff (presentationScalarEquiv S A e)

end FLT.Mazur.MatrixCokernel
