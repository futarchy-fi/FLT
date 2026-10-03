/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PrincipalUnitNorm
public import FLT.LocalClassFieldTheory.UnramifiedUniformizer
public import Mathlib.RingTheory.Trace.Basic

/-!
# One-step principal-unit norm corrections

Surjectivity of the separable residue trace supplies a correction at any
positive level. Both the correcting unit and its improved norm are constructed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  {π : R} (hπ : Irreducible π)

include hπ

/-- Every principal-unit symbol is the symbol of a norm. -/
theorem exists_principalNorm_symbol (n : ℕ) (hn : 0 < n) (u : principalUnits π n) :
    ∃ v : principalUnits (algebraMap R S π) n,
      residue R (principalCoeff π n (principalNorm R S π n v)) =
        residue R (principalCoeff π n u) := by
  obtain ⟨a, ha⟩ := Algebra.trace_surjective (ResidueField R) (ResidueField S)
    (residue R (principalCoeff π n u))
  obtain ⟨x, hx⟩ := residue_surjective a
  have hs := unramified_uniformizer_irreducible R S hπ
  let v := principalUnitOfCoeff (show algebraMap R S π ∈ maximalIdeal S from hs.not_isUnit)
    n hn x
  refine ⟨v, ?_⟩
  rw [principalNorm_residue R S hπ.ne_zero hπ.not_isUnit n hn,
    principalCoeff_ofCoeff hs.ne_zero, hx, ha]

/-- The norm error after a correction lies one step deeper. -/
theorem exists_principalNorm_correction (n : ℕ) (hn : 0 < n) (u : principalUnits π n) :
    ∃ v : principalUnits (algebraMap R S π) n,
      (principalNorm R S π n v).val / u.val ∈ principalUnits π (n + 1) := by
  obtain ⟨v, hv⟩ := exists_principalNorm_symbol R S hπ n hn u
  refine ⟨v, ?_⟩
  have hker : principalNorm R S π n v / u ∈
      (principalSymbol hπ.ne_zero hπ.not_isUnit n hn).ker := by
    change principalSymbol hπ.ne_zero hπ.not_isUnit n hn _ = 1
    rw [map_div, div_eq_one]
    exact congrArg Multiplicative.ofAdd hv
  rw [principalSymbol_ker _ _ _ _ hπ.maximalIdeal_eq] at hker
  exact hker

end LocalClassFieldTheory
