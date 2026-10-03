/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalExpEquivariance
public import FLT.LocalClassFieldTheory.NormalLatticeOpen

/-!
# Scaling the normal lattice into the exponential domain

The constructed normal lattice is integral. Multiplication by the nonzero
base scalar p² puts all of it strictly inside v(x) < v(p), and preserves
openness and the actual Galois action.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing IsDedekindDomain

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [CharZero L] [Fact p.Prime] in
/-- The residue-characteristic prime is strictly small in the fraction field. -/
theorem localExpRadius_lt_one : (dvrPrime S).valuation L (p : L) < 1 := by
  rw [← map_natCast (algebraMap S L), HeightOneSpectrum.valuation_lt_one_iff_mem]
  change (p : S) ∈ maximalIdeal S
  rw [← residue_eq_zero_iff, map_natCast]
  exact CharP.cast_eq_zero (ResidueField S) p

omit [CharZero L] in
/-- The constructed normal lattice lies in the valuation ring. -/
theorem integralNormalLattice_valuation_le_one (x : integralNormalLattice R K L) :
    (dvrPrime S).valuation L x.val ≤ 1 := by
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  let : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have hi : IsIntegral R x.val := integralNormalLattice_le_integralClosure R K L x.property
  obtain ⟨s, hs⟩ := (IsIntegralClosure.isIntegral_iff (R := R) (A := S)).mp hi
  rw [← hs]
  exact HeightOneSpectrum.valuation_le_one (dvrPrime S) s

/-- Scaling every lattice point by p² places it in the proved convergence ball. -/
theorem scaledNormalLattice_mem_domain (x : integralNormalLattice R K L) :
    (p : L) ^ 2 * x.val ∈ localExpDomain S L p := by
  change (dvrPrime S).valuation L ((p : L) ^ 2 * x.val) <
    (dvrPrime S).valuation L (p : L)
  rw [map_mul, map_pow]
  calc
    _ ≤ (dvrPrime S).valuation L (p : L) ^ 2 * 1 :=
      mul_le_mul' le_rfl (integralNormalLattice_valuation_le_one R S K L x)
    _ < (dvrPrime S).valuation L (p : L) := by
      rw [mul_one, pow_two]
      exact mul_lt_of_lt_one_right (localExpRadius_pos S L p) (localExpRadius_lt_one S L p)

/-- The explicit injective additive map of the lattice into the exponential domain. -/
def scaledNormalLatticeMap : integralNormalLattice R K L →+ localExpDomain S L p where
  toFun x := ⟨(p : L) ^ 2 * x.val, scaledNormalLattice_mem_domain R S K L p x⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' _ _ := Subtype.ext (mul_add _ _ _)

/-- The scaling map is injective because p² is nonzero. -/
theorem scaledNormalLatticeMap_injective :
    Function.Injective (scaledNormalLatticeMap R S K L p) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact mul_left_cancel₀ (pow_ne_zero 2
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) h'

omit [CharP (ResidueField S) p] in
/-- The scaled lattice is open in the actual fraction-field topology. -/
theorem scaledNormalLattice_isOpen :
    letI := dvrAdicValued S L
    IsOpen ((fun x : L => (p : L) ^ 2 * x) '' (integralNormalLattice R K L : Set L)) := by
  let := dvrAdicValued S L
  exact (Homeomorph.mulLeft₀ ((p : L) ^ 2)
    (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))).isOpenMap _
    (integralNormalLattice_isOpen R S K L)

end LocalClassFieldTheory
