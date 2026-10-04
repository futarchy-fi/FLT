/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ClosedIdealQuotient
public import FLT.Deformations.FinitePadicOrderTopology
public import FLT.GaloisRepresentation.HardlyRamified.LiftDomainFree
public import FLT.GaloisRepresentation.HardlyRamified.LiftPrimeAvoidingP

/-!
# Prime coefficient orders without normalization

A prime quotient of a Noetherian proartinian coefficient ring remains in the
same residue-field category. If the original ring is finite over the p-adic
integers and the prime avoids p, the quotient is a finite free characteristic-
zero domain, with its original quotient topology. Arithmetic finiteness and
nonnilpotence are explicit inputs, not conclusions of this construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace Deformation.ProartinianCat
variable {O : Type} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] (U : ProartinianCat O) [IsNoetherianRing U]
  (P : Ideal U) [P.IsPrime]

/-- The prime quotient with its original residue field and quotient topology. -/
abbrev primeCoefficientOrder : ProartinianCat O :=
  closedIdealQuotient U P (IsNoetherianRing.isClosed_ideal P) (Ideal.IsPrime.ne_top ‹_›)

/-- The continuous projection onto the same prime quotient. -/
def primeCoefficientOrderProjection : U ⟶ primeCoefficientOrder U P :=
  closedIdealQuotientHom U P (IsNoetherianRing.isClosed_ideal P) (Ideal.IsPrime.ne_top ‹_›)

/-- Every element of the coefficient order is the image of an original coefficient. -/
theorem primeCoefficientOrderProjection_surjective :
    Function.Surjective (primeCoefficientOrderProjection U P).hom :=
  Ideal.Quotient.mk_surjective

/-- The residue field is the original one, with its specified coefficient algebra. -/
def primeCoefficientOrderResidueEquiv :
    IsLocalRing.ResidueField O ≃ₐ[O] IsLocalRing.ResidueField (primeCoefficientOrder U P) :=
  IsResidueAlgebra.algEquiv O (primeCoefficientOrder U P)

variable (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] U] [Module.Finite ℤ_[p] U]

instance primeCoefficientOrderAlgebra : Algebra ℤ_[p] (primeCoefficientOrder U P) :=
  inferInstanceAs (Algebra ℤ_[p] (U ⧸ P))

instance primeCoefficientOrder_finite : Module.Finite ℤ_[p] (primeCoefficientOrder U P) :=
  inferInstanceAs (Module.Finite ℤ_[p] (U ⧸ P))

instance primeCoefficientOrder_domain : IsDomain (primeCoefficientOrder U P) :=
  inferInstanceAs (IsDomain (U ⧸ P))

instance primeCoefficientOrder_continuousSMul [ContinuousSMul ℤ_[p] U] :
    ContinuousSMul ℤ_[p] (primeCoefficientOrder U P) := by
  apply continuousSMul_of_algebraMap
  exact continuous_quot_mk.comp (continuous_algebraMap ℤ_[p] U)

/-- Avoiding p gives finite freeness over the original p-adic integers. -/
theorem primeCoefficientOrder_free (hp : (p : U) ∉ P) :
    Module.Free ℤ_[p] (primeCoefficientOrder U P) :=
  GaloisRepresentation.IsHardlyRamified.quotient_free_of_prime_avoiding_p p U P hp

/-- The constructed domain has characteristic zero. -/
theorem primeCoefficientOrder_charZero (hp : (p : U) ∉ P) :
    CharZero (primeCoefficientOrder U P) := by
  let := primeCoefficientOrder_free U P p hp
  exact charZero_of_injective_ringHom
    (Module.isTorsionFree_iff_algebraMap_injective.mp
      (inferInstance : Module.IsTorsionFree ℤ_[p] (primeCoefficientOrder U P)))

/-- The quotient topology is already the p-adic module topology. -/
theorem primeCoefficientOrder_isModuleTopology [ContinuousSMul ℤ_[p] U]
    (hp : (p : U) ∉ P) : IsModuleTopology ℤ_[p] (primeCoefficientOrder U P) := by
  let := primeCoefficientOrder_free U P p hp
  exact Deformation.finitePadicOrder_isModuleTopology p (primeCoefficientOrder U P)

/-- Nonnilpotence produces a prime quotient which is a finite free characteristic-zero domain.
The prime quotient construction above supplies its topology and original residue field. -/
theorem exists_primeCoefficientOrder (hp : ¬ IsNilpotent (p : U)) :
    ∃ P : Ideal U, ∃ _ : P.IsPrime, (p : U) ∉ P ∧
      Module.Finite ℤ_[p] (primeCoefficientOrder U P) ∧
      Module.Free ℤ_[p] (primeCoefficientOrder U P) ∧
      IsDomain (primeCoefficientOrder U P) ∧ CharZero (primeCoefficientOrder U P) := by
  obtain ⟨P, hP, hp⟩ := GaloisRepresentation.IsHardlyRamified.exists_prime_avoiding_p U p hp
  let := hP
  exact ⟨P, hP, hp, inferInstance, primeCoefficientOrder_free U P p hp,
    inferInstance, primeCoefficientOrder_charZero U P p hp⟩

end Deformation.ProartinianCat
