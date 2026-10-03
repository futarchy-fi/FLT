/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointsClosureChange

/-!
# Finite-flat models under a prescribed closure equivalence

The underlying additive group and coefficient module are retained. Only the
Galois action is conjugated, and the original Hopf model supplies the witness.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace GaloisModule

variable {R K Ω Ω' X : Type} [CommRing R] [Field K] [Field Ω] [Field Ω']
  [Algebra R K] [Algebra K Ω] [Algebra K Ω']
  [AddCommGroup X] [DistribMulAction (Ω ≃ₐ[K] Ω) X]

/-- The original point group, acted on through the specified closure equivalence. -/
def ClosureChangedPoints (_e : Ω ≃ₐ[K] Ω') (X : Type) := X

instance closureChangedPointsAddCommGroup (e : Ω ≃ₐ[K] Ω') :
    AddCommGroup (ClosureChangedPoints e X) :=
  inferInstanceAs (AddCommGroup X)

instance closureChangedPointsDistribMulAction (e : Ω ≃ₐ[K] Ω') :
    DistribMulAction (Ω' ≃ₐ[K] Ω') (ClosureChangedPoints e X) :=
  DistribMulAction.compHom X (AlgEquiv.autCongr e.symm).toMonoidHom

instance closureChangedPointsModule (e : Ω ≃ₐ[K] Ω') {k : Type} [Semiring k] [Module k X] :
    Module k (ClosureChangedPoints e X) := inferInstanceAs (Module k X)

instance closureChangedPointsSmulCommClass (e : Ω ≃ₐ[K] Ω')
    {k : Type} [Semiring k] [Module k X]
    [SMulCommClass k (Ω ≃ₐ[K] Ω) X] :
    SMulCommClass k (Ω' ≃ₐ[K] Ω') (ClosureChangedPoints e X) where
  smul_comm a σ x := smul_comm a (AlgEquiv.autCongr e.symm σ) (show X from x)

omit [DistribMulAction (Ω ≃ₐ[K] Ω) X] in
/-- The coefficient dimension is unchanged by closure transport. -/
theorem finrank_closureChangedPoints (e : Ω ≃ₐ[K] Ω')
    (k : Type) [DivisionRing k] [Module k X] :
    Module.finrank k (ClosureChangedPoints e X) = Module.finrank k X := rfl

/-- Conjugating the original automorphism retains its exact action on points. -/
theorem closureChangedPoints_smul (e : Ω ≃ₐ[K] Ω') (σ : Ω ≃ₐ[K] Ω) (x : X) :
    @SMul.smul _ (ClosureChangedPoints e X) inferInstance (AlgEquiv.autCongr e σ) x = σ • x := by
  change (AlgEquiv.autCongr e).symm (AlgEquiv.autCongr e σ) • x = _
  rw [MulEquiv.symm_apply_apply]

/-- Postcomposition transports the actual finite-flat witness to the new closure. -/
theorem IsFiniteFlat.closureChange (hX : IsFiniteFlat R K Ω X) (e : Ω ≃ₐ[K] Ω') :
    IsFiniteFlat R K Ω' (ClosureChangedPoints e X) := by
  rcases hX with ⟨H, _, _, _, _, f, hf⟩
  let a := hopfPointsClosureEquiv (A := K ⊗[R] H) e.symm
  let g : Additive (K ⊗[R] H →ₐ[K] Ω') →+[Ω' ≃ₐ[K] Ω'] ClosureChangedPoints e X :=
    { f.toAddMonoidHom.comp a.toAddMonoidHom with
      map_smul' := fun σ p ↦ by
        change f (a (σ • p)) = (AlgEquiv.autCongr e.symm σ) • f (a p)
        rw [hopfPointsClosureEquiv_smul]
        exact f.map_smul _ _ }
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, g,
    hf.comp a.bijective⟩

end GaloisModule
