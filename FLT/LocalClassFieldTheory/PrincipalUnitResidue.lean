/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PrincipalUnitFiltration

/-!
# The graded principal-unit quotient

For a generator π of the maximal ideal, `(1 + πⁿ a) ↦ ā` identifies
`Uⁿ / Uⁿ⁺¹` with the additive residue field, for every positive n.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {π : R} (hπ : π ≠ 0) (hm : π ∈ maximalIdeal R) (n : ℕ) (hn : 0 < n)

omit [IsDomain R] in
include hm hn in
/-- A positive power of an element of the maximal ideal has zero residue. -/
theorem residue_uniformizer_pow : residue R (π ^ n) = 0 := by
  rw [map_pow, (residue_eq_zero_iff _).2 hm, zero_pow (Nat.ne_of_gt hn)]

/-- The actual unit `1 + πⁿ a`. -/
def principalUnitOfCoeff (a : R) : principalUnits π n := by
  have hu : IsUnit (1 + π ^ n * a) :=
    (residue_ne_zero_iff_isUnit _).mp (by
      rw [map_add, map_one, map_mul, residue_uniformizer_pow hm n hn, zero_mul, add_zero]
      exact one_ne_zero)
  exact ⟨hu.unit, (mem_principalUnits π n hu.unit).2
    ⟨a, by rw [hu.unit_spec]; ring⟩⟩

omit [IsDomain R] in
/-- The constructed principal unit has the prescribed value. -/
@[simp] theorem principalUnitOfCoeff_val (a : R) :
    ((principalUnitOfCoeff hm n hn a).val : R) = 1 + π ^ n * a :=
  IsUnit.unit_spec _

include hπ in
/-- Its divided coefficient is exactly the chosen lift. -/
@[simp] theorem principalCoeff_ofCoeff (a : R) :
    principalCoeff π n (principalUnitOfCoeff hm n hn a) = a := by
  apply principalCoeff_eq hπ
  rw [principalUnitOfCoeff_val]
  ring

/-- Reduction of the divided coefficient, with an additive target. -/
def principalSymbol : principalUnits π n →* Multiplicative (ResidueField R) where
  toFun u := Multiplicative.ofAdd (residue R (principalCoeff π n u))
  map_one' := by
    change residue R (principalCoeff π n 1) = 0
    rw [principalCoeff_eq hπ n 1 0 (by simp), map_zero]
  map_mul' u v := by
    change residue R (principalCoeff π n (u * v)) =
      residue R (principalCoeff π n u) + residue R (principalCoeff π n v)
    rw [principalCoeff_mul hπ, map_add, map_add, map_mul, map_mul,
      residue_uniformizer_pow hm n hn, zero_mul, zero_mul, add_zero]

/-- Every residue class occurs as a principal-unit symbol. -/
theorem principalSymbol_surjective : Function.Surjective (principalSymbol hπ hm n hn) := by
  intro a
  obtain ⟨x, hx⟩ := residue_surjective (Multiplicative.toAdd a)
  refine ⟨principalUnitOfCoeff hm n hn x, ?_⟩
  change Multiplicative.ofAdd (residue R (principalCoeff π n _)) = a
  rw [principalCoeff_ofCoeff hπ, hx]
  rfl

/-- The kernel consists of the next principal-unit subgroup. -/
theorem principalSymbol_ker (hmax : maximalIdeal R = Ideal.span {π}) :
    (principalSymbol hπ hm n hn).ker =
      (principalUnits π (n + 1)).comap (principalUnits π n).subtype := by
  ext u
  change residue R (principalCoeff π n u) = 0 ↔ u.val ∈ principalUnits π (n + 1)
  rw [residue_eq_zero_iff, hmax, Ideal.mem_span_singleton,
    principalCoeff_dvd_iff hπ]

/-- The graded quotient is the additive residue field, as a group isomorphism. -/
def principalUnitsQuotientEquiv (hmax : maximalIdeal R = Ideal.span {π}) :
    principalUnits π n ⧸ (principalUnits π (n + 1)).comap (principalUnits π n).subtype ≃*
      Multiplicative (ResidueField R) :=
  (QuotientGroup.quotientMulEquivOfEq (principalSymbol_ker hπ hm n hn hmax).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (principalSymbol hπ hm n hn)
      (principalSymbol_surjective hπ hm n hn))

/-- The quotient isomorphism evaluates a representative by its divided coefficient. -/
theorem principalUnitsQuotientEquiv_mk
    (hmax : maximalIdeal R = Ideal.span {π}) (u : principalUnits π n) :
    principalUnitsQuotientEquiv hπ hm n hn hmax (QuotientGroup.mk u) =
      Multiplicative.ofAdd (residue R (principalCoeff π n u)) := rfl

end LocalClassFieldTheory
