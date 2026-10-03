/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTowerClosure

/-!
# Transporting automorphisms through the prescribed tower closure

An original automorphism fixing the embedded tower becomes an automorphism
over the tower field, with an explicit evaluation-intertwining identity.
-/

@[expose] public noncomputable section
namespace RaynaudParameters

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [IsAlgClosure K Ω]
  (e : L →ₐ[K] Ω)

/-- Conjugate an original automorphism fixing the tower through its closure equivalence. -/
def towerAutomorphism (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ a, σ (e a) = e a) :
    AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L :=
  { (towerClosureEquiv e).trans (σ.toRingEquiv.trans (towerClosureEquiv e).symm) with
    commutes' := fun a ↦ by
      apply (towerClosureEquiv e).injective
      change towerClosureEquiv e ((towerClosureEquiv e).symm
        (σ (towerClosureEquiv e (algebraMap L (AlgebraicClosure L) a)))) = _
      rw [RingEquiv.apply_symm_apply, towerClosureEquiv_algebraMap, hσ] }

/-- Evaluation in the original closure intertwines the transported automorphism. -/
theorem towerAutomorphism_apply (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ a, σ (e a) = e a)
    (x : AlgebraicClosure L) :
    towerClosureEquiv e (towerAutomorphism e σ hσ x) = σ (towerClosureEquiv e x) :=
  (towerClosureEquiv e).apply_symm_apply _

/-- The identity original automorphism transports to the identity. -/
theorem towerAutomorphism_one :
    towerAutomorphism e 1 (fun _ ↦ rfl) = 1 := by
  ext x
  apply (towerClosureEquiv e).injective
  exact towerAutomorphism_apply e 1 (fun _ ↦ rfl) x

/-- Conjugation respects products independently of proofs of tower fixedness. -/
theorem towerAutomorphism_mul (σ τ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ a, σ (e a) = e a) (hτ : ∀ a, τ (e a) = e a) :
    towerAutomorphism e (σ * τ) (fun a ↦ by simp [AlgEquiv.mul_apply, hσ, hτ]) =
      towerAutomorphism e σ hσ * towerAutomorphism e τ hτ := by
  ext x
  apply (towerClosureEquiv e).injective
  simp only [AlgEquiv.mul_apply, towerAutomorphism_apply]

end RaynaudParameters
