/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.LocalizedResidueKernel

/-! # Construct the residue-fibre point of an original presentation -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace Ideal

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- An original prime is the contraction of a point of its actual residue fibre. -/
theorem exists_residue_fibre_prime (Q : Ideal A) [Q.IsPrime] :
    ∃ (q : Ideal ((Q.comap (algebraMap R A)).Fiber A)) (_ : q.IsPrime),
      q.comap (includeRight : A →ₐ[R] (Q.comap (algebraMap R A)).Fiber A) = Q := by
  let p : PrimeSpectrum R := ⟨Q.comap (algebraMap R A), inferInstance⟩
  let P : PrimeSpectrum.comap (algebraMap R A) ⁻¹' {p} := ⟨⟨Q, inferInstance⟩, rfl⟩
  let q := PrimeSpectrum.preimageEquivFiber R A p P
  refine ⟨q.asIdeal, q.isPrime, ?_⟩
  have h := congrArg (fun x ↦ (x.val : PrimeSpectrum A).asIdeal)
    ((PrimeSpectrum.preimageEquivFiber R A p).symm_apply_apply P)
  exact h

end Ideal

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- A target prime supplies a source fibre prime containing the entire fibre kernel.
Its contraction is exactly the prime of the original localized presentation. -/
theorem exists_residue_presentation_prime (f : S →ₐ[R] A) (Q : Ideal A) [Q.IsPrime] :
    let p := Q.comap (algebraMap R A)
    ∃ (q : Ideal (p.Fiber S)) (_ : q.IsPrime),
      q.comap includeRight = Q.comap (f : S →+* A) ∧
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R p.ResidueField) f) ≤ q := by
  dsimp only
  let p := Q.comap (algebraMap R A)
  obtain ⟨qA, hqA, hq⟩ := Ideal.exists_residue_fibre_prime (R := R) Q
  let F := Algebra.TensorProduct.map (AlgHom.id R p.ResidueField) f
  refine ⟨qA.comap F, inferInstance, ?_, Ideal.ker_le_comap F⟩
  have hc : (qA.comap F).comap includeRight = (qA.comap includeRight).comap f := by
    ext s
    change F (1 ⊗ₜ[R] s) ∈ qA ↔ (1 ⊗ₜ[R] f s) ∈ qA
    simp [F]
  rw [hc, hq]
  rfl

end AlgHom
