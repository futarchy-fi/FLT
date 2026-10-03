/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudStrictHenselian

/-!
# Placing a tower closure in the original closure

The equivalence extends the prescribed fraction-field embedding, rather than
an independently chosen embedding of the tower.
-/

@[expose] public noncomputable section

namespace RaynaudParameters

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [IsAlgClosure K Ω]

/-- Extend a prescribed embedding of a tower field to its algebraic closure. -/
def towerClosureEquiv (e : L →ₐ[K] Ω) : AlgebraicClosure L ≃+* Ω := by
  letI : Algebra L Ω := e.toRingHom.toAlgebra
  letI : IsScalarTower K L Ω := .of_algebraMap_eq fun x ↦ (e.commutes x).symm
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  letI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  letI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L (A := Ω)
  letI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  exact (IsAlgClosure.equiv L (AlgebraicClosure L) Ω).toRingEquiv

/-- The closure equivalence retains the specified copy of every tower element. -/
theorem towerClosureEquiv_algebraMap (e : L →ₐ[K] Ω) (x : L) :
    towerClosureEquiv e (algebraMap L (AlgebraicClosure L) x) = e x := by
  let : Algebra L Ω := e.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := .of_algebraMap_eq fun x ↦ (e.commutes x).symm
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  let : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L (A := Ω)
  let : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  exact (IsAlgClosure.equiv L (AlgebraicClosure L) Ω).commutes x

/-- In particular, the equivalence fixes the original ground field. -/
theorem towerClosureEquiv_base (e : L →ₐ[K] Ω) (x : K) :
    towerClosureEquiv e (algebraMap K (AlgebraicClosure L) x) = algebraMap K Ω x := by
  rw [IsScalarTower.algebraMap_apply K L (AlgebraicClosure L),
    towerClosureEquiv_algebraMap, e.commutes]

end RaynaudParameters
