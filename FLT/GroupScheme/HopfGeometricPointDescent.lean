/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfGeometricPresentationDescent

/-! # Regular original relations at a specified geometric fibre point -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k K A H : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
  [CommRing A] [Algebra k A] [CommRing H] [HopfAlgebra K H]
  [IsArtinianRing H] [Module.Finite K H]
  (p : ℕ) [Fact p.Prime] [CharP K p]

include p

/-- Translate the actual fibre point through the geometric comparison internally.
The resulting local ring is determined by the original coordinate values. -/
theorem exists_original_relations_at_fibre_point {n : ℕ}
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f)
    (e : K ⊗[k] A ≃ₐ[K] H) (y : A →ₐ[k] K) :
    ∃ rs : List (GeometricPointSource k K (fun i ↦ y (f (X i)))), rs.length = n ∧
      Ideal.ofList rs = (RingHom.ker f).map
        (algebraMap _ (GeometricPointSource k K (fun i ↦ y (f (X i))))) ∧
      RingTheory.Sequence.IsRegular (GeometricPointSource k K (fun i ↦ y (f (X i)))) rs := by
  let z : K ⊗[k] A →ₐ[K] K :=
    Algebra.TensorProduct.lift (AlgHom.id K K) y (fun _ _ ↦ Commute.all _ _)
  let ε := z.comp e.symm.toAlgHom
  have ha : (fun i ↦ ε (e (1 ⊗ₜ f (X i)))) = (fun i ↦ y (f (X i))) := by
    funext i
    simp [ε, z]
  have h := exists_original_fibre_regular_relations p f hf e ε
  dsimp only at h
  exact ha ▸ h

end HopfAlgebra
