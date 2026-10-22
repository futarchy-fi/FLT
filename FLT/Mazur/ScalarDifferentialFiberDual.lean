/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFiniteTypeFiberTests
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Testing differential fibers by residue-valued derivations

The dual of a differential fiber consists of derivations into the residue
field with its actual source action. Its vanishing detects the full fiber,
without any finite-dimensional assumption. Nilpotent source directions are
retained, since the derivations are taken on the full source ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarDifferentialFiberDual
open TensorProduct
variable {R A K : Type} [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

/-- Universal differentials identify residue-valued derivations with the dual fiber. -/
def derivationEquivDual :
    Derivation R A K ≃ Module.Dual K (K ⊗[A] KaehlerDifferential R A) :=
  (KaehlerDifferential.linearMapEquivDerivation R A).symm.toEquiv.trans
    (LinearMap.liftBaseChangeEquiv K).toEquiv

/-- Residue-valued derivations detect every direction in the differential fiber. -/
theorem fiber_subsingleton_iff :
    Subsingleton (K ⊗[A] KaehlerDifferential R A) ↔ Subsingleton (Derivation R A K) := by
  rw [← Module.subsingleton_dual_iff K]
  exact (derivationEquivDual (R := R) (A := A) (K := K)).subsingleton_congr.symm

variable {B : Type} [CommRing B]

omit [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] in
/-- The criterion uses the original scalar map and the exact target residue action. -/
theorem fiberVanishes_iff (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) :
    ScalarFiniteTypeFiberTests.FiberVanishes σ φ Q ↔
      let _ := σ.toAlgebra
      let ρ := (algebraMap B Q.asIdeal.ResidueField).comp φ
      let _ := ρ.toAlgebra
      let _ := (ρ.comp σ).toAlgebra
      Subsingleton (Derivation R A Q.asIdeal.ResidueField) := by
  let _ := σ.toAlgebra
  let ρ := (algebraMap B Q.asIdeal.ResidueField).comp φ
  let _ := ρ.toAlgebra
  let _ := (ρ.comp σ).toAlgebra
  let _ : IsScalarTower R A Q.asIdeal.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  exact fiber_subsingleton_iff

end FLT.Mazur.ScalarDifferentialFiberDual
