/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialPolynomial
public import FLT.GaloisRepresentation.HardlyRamified.TraceReducibility
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The standard split lift cannot lift an irreducible residual representation

The trace identity survives arbitrary field-valued coefficient reduction and
any change of basis. Thus a cyclotomic-plus-trivial point cannot supply the
residual compatibility required by the irreducible HR deformation problem.
This does not rule out representations which are ordinary only locally at p.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]

/-- The split integral representation has trace one plus determinant. -/
theorem cyclotomicTrivial_trace (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.trace ℤ_[p] _ (cyclotomicTrivial p g) =
      1 + (cyclotomicTrivial p g).det := by
  rw [cyclotomicTrivial_eq_prodMap, LinearMap.trace_prodMap', LinearMap.det_prodMap]
  have hm : LinearMap.mulLeft ℤ_[p] (integralCyclotomicScalar p g) =
      integralCyclotomicScalar p g • (LinearMap.id : Module.End ℤ_[p] ℤ_[p]) := by
    exact LinearMap.ext fun _ ↦ rfl
  rw [hm]
  simp [add_comm]

variable (k : Type*) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [Algebra ℤ_[p] k] [ContinuousSMul ℤ_[p] k]
  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  (e : k ⊗[ℤ_[p]] (ℤ_[p] × ℤ_[p]) ≃ₗ[k] V)

/-- Even after an arbitrary framing, the reduced split representation is reducible. -/
theorem cyclotomicTrivial_baseChange_conj_not_irreducible :
    ¬ ((cyclotomicTrivial p).baseChange k |>.conj e).IsIrreducible := by
  have hr : Module.rank k (k ⊗[ℤ_[p]] (ℤ_[p] × ℤ_[p])) = 2 := by
    simpa only [Module.rank_baseChange, Cardinal.lift_ofNat] using
      congrArg Cardinal.lift (cyclotomicTrivial_rank p)
  have hd : Module.finrank k V = 2 :=
    e.finrank_eq.symm.trans (Module.finrank_eq_of_rank_eq hr)
  apply B5Inputs.not_isIrreducible_of_trace_eq_one_add_det hd
  intro g
  change LinearMap.trace k V (e.conj ((cyclotomicTrivial p g).baseChange k)) =
    1 + (e.conj ((cyclotomicTrivial p g).baseChange k)).det
  have hdet : (e.conj ((cyclotomicTrivial p g).baseChange k)).det =
      ((cyclotomicTrivial p g).baseChange k).det := by
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
      LinearMap.det_conj ((cyclotomicTrivial p g).baseChange k) e
  rw [LinearMap.trace_conj', hdet, LinearMap.trace_baseChange,
    LinearMap.det_baseChange, cyclotomicTrivial_trace, map_add, map_one]

/-- The residual matching equation fails for every irreducible target. -/
theorem cyclotomicTrivial_baseChange_conj_ne (ρ : GaloisRep ℚ k V)
    (hirr : ρ.IsIrreducible) : ((cyclotomicTrivial p).baseChange k).conj e ≠ ρ := by
  intro he
  exact cyclotomicTrivial_baseChange_conj_not_irreducible p k e (he ▸ hirr)

end GaloisRepresentation
