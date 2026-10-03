/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatClosureChange
public import FLT.GroupScheme.FiniteFlatSubquotientBaseChange

/-!
# Integral base change followed by a prescribed closure comparison

The closure equivalence is arbitrary, allowing the original completion's
chosen tower equivalence to be used after finite inertia descent.
-/

@[expose] public noncomputable section
namespace GaloisModule

variable {R S K L Ω Ω' X : Type} [CommRing R] [CommRing S] [Field K] [Field L]
  [Field Ω] [Field Ω'] [Algebra R K] [Algebra R S] [Algebra K L] [Algebra S L]
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
  [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [Algebra L Ω']
  [AddCommGroup X] [DistribMulAction (Ω ≃ₐ[K] Ω) X]

/-- Integral base change preserves scalar commutation on the original point type. -/
instance restrictedPoints_smulCommClass {k : Type} [Semiring k] [Module k X]
    [SMulCommClass k (Ω ≃ₐ[K] Ω) X] :
    SMulCommClass k (Ω ≃ₐ[L] Ω) (RestrictedPoints K L Ω X) where
  smul_comm a σ x := smul_comm a (σ.restrictScalars K) (show X from x)

/-- The actual model transports through any specified closure equivalence. -/
theorem IsFiniteFlat.baseChange_prescribedClosure (hX : IsFiniteFlat R K Ω X)
    (c : Ω' ≃ₐ[L] Ω) :
    IsFiniteFlat S L Ω' (ClosureChangedPoints c.symm (RestrictedPoints K L Ω X)) :=
  (hX.baseChange_sameClosure (S := S) (L := L)).closureChange c.symm

/-- The changed point action is exactly conjugation followed by restriction. -/
theorem prescribedClosurePoints_smul (c : Ω' ≃ₐ[L] Ω) (τ : Ω' ≃ₐ[L] Ω') (x : X) :
    @SMul.smul _ (ClosureChangedPoints c.symm (RestrictedPoints K L Ω X)) inferInstance τ x =
      (AlgEquiv.autCongr c τ).restrictScalars K • x := rfl

end GaloisModule
