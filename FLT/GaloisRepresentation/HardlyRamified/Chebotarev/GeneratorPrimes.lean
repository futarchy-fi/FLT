/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder

/-! # Primes whose Frobenius generates the Galois group -/

@[expose] public section

namespace GaloisRepresentation.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Unramified primes whose Frobenius generates the Galois group. -/
def Generators : Set (Prime K) :=
  {v | Unram K L v ∧ Subgroup.zpowers (frob K L v) = ⊤}

end GaloisRepresentation.Chebotarev
