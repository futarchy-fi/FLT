/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteArtin

/-!
# Positive normalization of finite reciprocity

The existing inverse positive Tate cup has the inverse-Frobenius convention.
Negating its additive abelianization value defines positive reciprocity while
preserving its proved surjectivity and algebraic norm kernel.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

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

/-- Finite reciprocity with the explicit negative inverse-cup normalization. -/
def positiveFiniteArtin : Additive Kˣ →+ Additive (Abelianization Gal(F/K)) :=
  -finiteArtin R S K C F p

/-- Positive reciprocity differs from the existing Artin map by exactly one negation. -/
theorem positiveFiniteArtin_apply (u : Additive Kˣ) :
    positiveFiniteArtin R S K C F p u = -finiteArtin R S K C F p u := rfl

/-- The positive normalization remains surjective. -/
theorem positiveFiniteArtin_surjective : Function.Surjective (positiveFiniteArtin R S K C F p) := by
  intro a
  obtain ⟨u, hu⟩ := finiteArtin_surjective R S K C F p (-a)
  exact ⟨u, by rw [positiveFiniteArtin_apply, hu, neg_neg]⟩

/-- Changing normalization preserves exactly the algebraic norm kernel. -/
theorem positiveFiniteArtin_eq_zero_iff (u : Additive Kˣ) :
    positiveFiniteArtin R S K C F p u = 0 ↔
      ∃ v : Fˣ, Units.map (Algebra.norm K) v = Additive.toMul u := by
  rw [positiveFiniteArtin_apply, neg_eq_zero, finiteArtin_eq_zero_iff]

end LocalClassFieldTheory
