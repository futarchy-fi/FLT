/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SemilinearScalarRecovery
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Integral Galois coordinates from a unit evaluation determinant

Fixed coefficients construct the trace map; an invertible evaluation matrix
constructs the orthogonality coordinates. These are conditions on the base
extension alone, independent of the algebra being descended. In particular,
no inverse to its scalar-extension map is supplied as input.
-/

@[expose] public noncomputable section
open scoped BigOperators TensorProduct
namespace SemilinearDescent

universe u
variable {R S : Type u} {G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [Fintype G] (σ : G →* (S ≃ₐ[R] S))
  (hinj : Function.Injective (algebraMap R S))
  (hfixed : ∀ s : S, (∀ g, σ g s = s) → ∃ r, algebraMap R S r = s)

omit [Fintype G] in
/-- Fixed scalar descent as an algebra equivalence. -/
def fixedScalars : R ≃ₐ[R] fixed σ :=
  AlgEquiv.ofBijective (Algebra.ofId R (fixed σ)) ⟨fun _ _ h ↦
    hinj (congrArg Subtype.val h), fun s ↦ by
      obtain ⟨r, hr⟩ := hfixed s s.property
      exact ⟨r, Subtype.ext hr⟩⟩

/-- The coefficient trace is the orbit sum expressed in base scalars. -/
def coefficientTrace : S →ₗ[R] R :=
  (fixedScalars σ hinj hfixed).symm.toLinearMap.comp (orbitSum σ)

/-- The constructed trace has the required orbit-sum formula. -/
theorem coefficientTrace_spec (s : S) :
    algebraMap R S (coefficientTrace σ hinj hfixed s) = ∑ g, σ g s := by
  exact congrArg Subtype.val ((fixedScalars σ hinj hfixed).apply_symm_apply (orbitSum σ s))

variable [DecidableEq G]

/-- The Galois evaluation matrix of integral coefficient elements. -/
def evaluationMatrix (b : G → S) : Matrix G G S := fun g i ↦ σ g (b i)

/-- A unit determinant constructs integral orthogonality coordinates. -/
theorem evaluationMatrix_coordinates (b : G → S)
    (hdet : IsUnit (evaluationMatrix σ b).det) (g : G) :
    ∑ i, (evaluationMatrix σ b)⁻¹ i 1 * σ g (b i) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun M : Matrix G G S ↦ M g 1)
    (Matrix.mul_nonsing_inv (evaluationMatrix σ b) hdet)
  simpa only [Matrix.mul_apply, Matrix.one_apply, evaluationMatrix, mul_comm] using h

variable {B : Type u} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (ρ : G →* (B ≃ₐ[R] B))
  (hρ : ∀ g s, ρ g (algebraMap S B s) = algebraMap S B (σ g s))

include hinj hfixed hρ in
/-- An integral unit evaluation determinant proves effective algebra descent. -/
theorem integral_recoveryMap_bijective (b : G → S)
    (hdet : IsUnit (evaluationMatrix σ b).det) :
    Function.Bijective (recoveryMap (S := S) ρ) :=
  recoveryMap_bijective σ ρ hρ (fun i ↦ (evaluationMatrix σ b)⁻¹ i 1) b
    (evaluationMatrix_coordinates σ b hdet) (coefficientTrace σ hinj hfixed)
    (coefficientTrace_spec σ hinj hfixed)

end SemilinearDescent
