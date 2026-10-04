/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicCharacterArtin

/-!
# The absolute invariant of a faithful cyclic parameter carry

The proved cyclic Artin coordinate and the normalization of the independent
fundamental class give the character evaluation, including degree one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory groupCohomology

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  [Algebra S F] [IsFractionRing S F] [Algebra S C] [IsScalarTower S F C]
  [IsScalarTower R S F] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

local notation "M" => Rep.ofAlgebraAutOnUnits K F

variable {n : ℕ} [NeZero n] (χ : Gal(F/K) →* Multiplicative (ZMod n))
  (hχ : Function.Bijective χ) (u : Additive Kˣ)

local notation "x" => finiteUnitInvariantInclusion K F u
local notation "c" => finiteParameterCarryClass χ (Additive Fˣ) x

omit [Algebra.IsSeparable K C] [IsSepClosed C]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)] [CharZero C] in
include hχ in
/-- The character's cyclic order equals the actual field degree. -/
theorem cyclicCharacter_finrank : Module.finrank K F = n := by
  rw [← IsGalois.card_aut_eq_finrank K F]
  exact (Nat.card_congr (Equiv.ofBijective χ hχ)).trans (by simp)

include hχ in
/-- The absolute invariant of the positive carry evaluates positive finite reciprocity. -/
theorem cyclicCarry_artin_invariant :
    absoluteInvariant R K C p ((galoisMultiplicativeInflation K C F 2).hom c) =
      zmodToRatCircle n
        (finiteCharacterAbelianization χ (positiveFiniteArtin R S K C F p u)) := by
  by_cases hn : 1 < n
  · obtain ⟨m, hm, ha⟩ := cyclicCharacterArtin_coordinate R S K C F p χ hχ u hn
    rw [← hm, map_nsmul, map_nsmul, relativeFundamentalClass_inflation R S K C F p,
      absoluteFundamentalClass_invariant, cyclicCharacter_finrank K C F χ hχ, ha]
    have h1 : zmodToRatCircle n 1 = (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) := by
      simpa using zmodToRatCircle_intCast n 1
    rw [← h1, ← map_nsmul]
    congr 1
    simp
  · have he : n = 1 := by have := NeZero.pos n; omega
    have hz : c = 0 := by
      obtain ⟨m, hm⟩ := finiteParameterCarry_fundamental_multiple R S K C F p χ u
      have hd : Module.finrank K F = 1 := (cyclicCharacter_finrank K C F χ hχ).trans he
      have hf : relativeFundamentalClass R S K C F = 0 := by
        apply (AddMonoid.addOrderOf_eq_one_iff).mp
        exact (relativeFundamentalClass_order R S K C F).trans hd
      rw [← hm, hf, smul_zero]
    rw [hz, map_zero, map_zero]
    have hval : finiteCharacterAbelianization χ (positiveFiniteArtin R S K C F p u) = 0 := by
      subst n
      exact Subsingleton.elim _ _
    rw [hval, map_zero]

end LocalClassFieldTheory
