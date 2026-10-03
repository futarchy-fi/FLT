/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteUnitInvariants
public import FLT.LocalClassFieldTheory.RelativeFundamentalCupIso
public import FLT.LocalClassFieldTheory.TateInvariantClass
public import FLT.LocalClassFieldTheory.TateScalarAbelianization

/-!
# The finite local Artin map

The inverse fundamental cup and the canonical scalar abelianization
comparison define the finite Artin map. It is surjective, and its kernel is
exactly the algebraic norm subgroup.
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

/-- The additive form of the finite Artin map, constructed from the inverse fundamental cup. -/
def finiteArtin : Additive Kˣ →+ Additive (Abelianization Gal(F/K)) :=
  (tateScalarAbelianizationEquiv Gal(F/K)).toAddMonoidHom.comp
    ((relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm.toAddMonoidHom.comp
      ((tateInvariantClass M).hom.toAddMonoidHom.comp
        (finiteUnitInvariantInclusion K F).toAddMonoidHom))

/-- The finite Artin map is surjective onto the abelianized finite Galois group. -/
theorem finiteArtin_surjective : Function.Surjective (finiteArtin R S K C F p) :=
  (tateScalarAbelianizationEquiv Gal(F/K)).surjective.comp
    ((relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm.surjective.comp
      ((tateInvariantClass_surjective M).comp (finiteUnitInvariantInclusion_surjective K F)))

/-- The Artin kernel consists exactly of field norms, with no norm-kernel hypothesis. -/
theorem finiteArtin_eq_zero_iff (u : Additive Kˣ) :
    finiteArtin R S K C F p u = 0 ↔
      ∃ v : Fˣ, Units.map (Algebra.norm K) v = Additive.toMul u := by
  change (tateScalarAbelianizationEquiv Gal(F/K))
    ((relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm
      (tateInvariantClass M (finiteUnitInvariantInclusion K F u))) = 0 ↔ _
  rw [map_eq_zero_iff _ (tateScalarAbelianizationEquiv Gal(F/K)).injective,
    map_eq_zero_iff _ (relativeFundamentalTateCupNegTwoEquiv R S K C F p).symm.injective,
    tateInvariantClass_eq_zero_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Additive.toMul v, ?_⟩
    apply Additive.ofMul.injective
    apply finiteUnitInvariantInclusion_injective K F
    apply Subtype.ext
    exact (finiteUnitInvariant_norm K F (Additive.toMul v)).trans hv
  · rintro ⟨v, hv⟩
    refine ⟨Additive.ofMul v, ?_⟩
    rw [← finiteUnitInvariant_norm, hv]
    rfl

/-- Every algebraic norm has trivial finite Artin image. -/
theorem finiteArtin_norm (v : Fˣ) :
    finiteArtin R S K C F p (Additive.ofMul (Units.map (Algebra.norm K) v)) = 0 :=
  (finiteArtin_eq_zero_iff R S K C F p _).mpr ⟨v, rfl⟩

end LocalClassFieldTheory
