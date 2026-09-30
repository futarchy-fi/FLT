/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.LiftDomainFree
public import FLT.GaloisRepresentation.HardlyRamified.PrimeResidualNaturality

/-!
# Residue-compatible finite free coefficient quotients

A prime quotient avoiding p keeps the original prime residual coefficient
field. The input ring need only be finite over the p-adic integers, not free.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

variable (p : ℕ) [Fact p.Prime] (D : Type)
  [CommRing D] [IsLocalRing D] [Algebra ℤ_[p] D]
  [IsLocalHom (algebraMap ℤ_[p] D)] [IsResidueAlgebra ℤ_[p] D]
  (P : Ideal D) [P.IsPrime]

local instance : IsLocalHom (algebraMap ℤ_[p] (D ⧸ P)) := by
  let : IsLocalHom (Ideal.Quotient.mk P) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  change IsLocalHom ((Ideal.Quotient.mk P).comp (algebraMap ℤ_[p] D))
  infer_instance

/-- Taking a prime quotient preserves the specified prime-field reduction. -/
theorem primeReduction_quotient_comp :
    (primeReduction p (D ⧸ P)).comp (Ideal.Quotient.mk P) = primeReduction p D :=
  primeReduction_natural p D (D ⧸ P) _

/-- A prime quotient avoiding p is free and has a local algebra map to the original
prime residue field, compatible with the given p-adic coefficient algebra. -/
theorem exists_quotient_residual_algebra [Module.Finite ℤ_[p] D]
    (hp : (p : D) ∉ P) [Algebra ℤ_[p] (ZMod p)] :
    ∃ (_ : Algebra (D ⧸ P) (ZMod p)),
      IsScalarTower ℤ_[p] (D ⧸ P) (ZMod p) ∧
      IsLocalHom (algebraMap (D ⧸ P) (ZMod p)) ∧
      Module.Free ℤ_[p] (D ⧸ P) := by
  let f := primeReduction p (D ⧸ P)
  let : Algebra (D ⧸ P) (ZMod p) := f.toAlgebra
  refine ⟨inferInstance, ?_, ?_, quotient_free_of_prime_avoiding_p p D P hp⟩
  · apply IsScalarTower.of_algebraMap_eq'
    exact (primeResidueMap_unique p _).trans
      (primeReduction_comp_algebraMap p (D ⧸ P)).symm
  · exact IsLocalHom.of_surjective f (primeReduction_surjective p (D ⧸ P))

end GaloisRepresentation.IsHardlyRamified
