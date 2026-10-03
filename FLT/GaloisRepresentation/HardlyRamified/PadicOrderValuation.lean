/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PadicOrderAlgebra

/-!
# General-prime order normalization: Valuation

The construction retains the original order and its fraction field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PadicOrderPlan
open scoped nonZeroDivisors

variable (p : ℕ) [Fact p.Prime]
variable (R : Type*) [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
  [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]

/-- The spectral norm extending the p-adic norm. -/
@[instance_reducible]
def fractionNormedField : NontriviallyNormedField (FractionRing R) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] (FractionRing R)

/-- The spectral norm respects scalar multiplication by the p-adic field. -/
@[instance_reducible]
def fractionNormedAlgebra :
    letI := fractionNormedField p R
    NormedAlgebra ℚ_[p] (FractionRing R) :=
  spectralNorm.normedAlgebra ℚ_[p] (FractionRing R)

/-- Integrality over the p-adic integers is exactly the closed unit ball condition. -/
theorem isIntegral_iff_norm_le_one (x : FractionRing R) :
    IsIntegral ℤ_[p] x ↔ spectralNorm ℚ_[p] (FractionRing R) x ≤ 1 := by
  rw [spectralNorm, spectralValue_le_one_iff
    (minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) x))]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hx, Polynomial.coeff_map]
    exact ((minpoly ℤ_[p] x).coeff n).property
  · intro hx
    have hlift : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hx n⟩, rfl⟩
    obtain ⟨f, hf, _, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
      (minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) x))
    refine ⟨f, hm, ?_⟩
    change Polynomial.aeval x f = 0
    rw [← Polynomial.aeval_map_algebraMap ℚ_[p], hf]
    exact minpoly.aeval ℚ_[p] x

/-- The normalization, viewed as a valuation subring of its fraction field. -/
def normalizedValuationSubring : ValuationSubring (FractionRing R) where
  toSubring := (integralClosure ℤ_[p] (FractionRing R)).toSubring
  mem_or_inv_mem' x := by
    change IsIntegral ℤ_[p] x ∨ IsIntegral ℤ_[p] x⁻¹
    simp only [isIntegral_iff_norm_le_one p R]
    let := fractionNormedField p R
    change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
    rw [norm_inv]
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)

/-- The normalization is local. -/
theorem normalizedOrder_isLocalRing : IsLocalRing (NormalizedOrder p R) :=
  inferInstanceAs (IsLocalRing (normalizedValuationSubring p R))

attribute [scoped instance] normalizedOrder_isLocalRing

/-- The normalization cannot be a field, since it is integral over `ℤ_[p]`. -/
theorem normalizedOrder_not_isField : ¬ IsField (NormalizedOrder p R) := by
  intro h
  exact IsDiscreteValuationRing.not_isField ℤ_[p]
    (isField_of_isIntegral_of_isField
      (FaithfulSMul.algebraMap_injective ℤ_[p] (NormalizedOrder p R)) h)

/-- The normalization is a discrete valuation ring. -/
theorem normalizedOrder_isDiscreteValuationRing : IsDiscreteValuationRing (NormalizedOrder p R) :=
  ((IsDiscreteValuationRing.TFAE (NormalizedOrder p R)
    (normalizedOrder_not_isField p R)).out 3 1).mp
      (inferInstance : IsDedekindDomain (NormalizedOrder p R))

/-- The normalization has a finite residue field. -/
theorem normalizedOrder_finite_residueField :
    Finite (IsLocalRing.ResidueField (NormalizedOrder p R)) :=
  IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[p]) (S := NormalizedOrder p R)
    (Finite.of_equiv (ZMod p) (PadicInt.residueField).symm.toEquiv)

/-- The normalization's residue field has characteristic p. -/
theorem normalizedOrder_residueField_charP :
    CharP (IsLocalRing.ResidueField (NormalizedOrder p R)) p := by
  have := normalizedOrder_finite_residueField p R
  exact ThreeAdicPlan.charP_of_finite_padic_algebra p _

attribute [scoped instance] normalizedOrder_isDiscreteValuationRing
  normalizedOrder_finite_residueField normalizedOrder_residueField_charP

end PadicOrderPlan
