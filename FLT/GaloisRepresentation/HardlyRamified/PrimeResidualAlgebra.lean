/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.IsResidueAlgebra
public import FLT.GaloisRepresentation.HardlyRamified.PrimeResidueMap

/-! # Prime residue fields of deformation coefficient algebras -/

@[expose] public noncomputable section

namespace GaloisRepresentation.IsHardlyRamified

variable (p : ℕ) [Fact p.Prime] (D : Type*)
  [CommRing D] [IsLocalRing D] [Algebra ℤ_[p] D]
  [IsLocalHom (algebraMap ℤ_[p] D)] [IsResidueAlgebra ℤ_[p] D]

/-- Identify the residue field of a same-residue p-adic algebra with the prime field. -/
def primeResidueEquiv : IsLocalRing.ResidueField D ≃+* ZMod p :=
  (IsResidueAlgebra.algEquiv ℤ_[p] D).symm.toRingEquiv.trans PadicInt.residueField

/-- The prime-field reduction of a deformation coefficient algebra. -/
def primeReduction : D →+* ZMod p :=
  (primeResidueEquiv p D).toRingHom.comp (IsLocalRing.residue D)

/-- Prime-field reduction is onto. -/
theorem primeReduction_surjective : Function.Surjective (primeReduction p D) :=
  (primeResidueEquiv p D).surjective.comp IsLocalRing.residue_surjective

/-- Prime-field reduction kills exactly the maximal ideal. -/
theorem primeReduction_ker :
    RingHom.ker (primeReduction p D) = IsLocalRing.maximalIdeal D :=
  IsLocalRing.ker_eq_maximalIdeal _ (primeReduction_surjective p D)

/-- The coefficient map followed by reduction is the canonical p-adic residue map. -/
theorem primeReduction_comp_algebraMap :
    (primeReduction p D).comp (algebraMap ℤ_[p] D) = PadicInt.toZMod :=
  primeResidueMap_unique p _

end GaloisRepresentation.IsHardlyRamified
