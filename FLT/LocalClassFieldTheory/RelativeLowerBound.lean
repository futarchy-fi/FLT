/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeDegreeTorsionClass

/-!
# The cyclic lower subgroup in relative multiplicative H2

Inflation injectivity makes the constructed relative preimages additive
and distinct. Composing with positive rational torsion coordinates embeds
Z/[E:K] in actual relative H2, without assuming its finiteness or order.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) [IsGalois K E]
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C
local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)))

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [FiniteDimensional K E]

local notation "d" => Module.finrank K E

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

/-- The unique relative preimages assemble into an additive map from the degree kernel. -/
def relativeDegreeTorsionHom : relativeRestrictionKernel d →+
    continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 where
  toFun := relativeDegreeTorsionClass R S K C E
  map_zero' := by
    apply galoisMultiplicativeInflationH2_injective K C E
    rw [relativeDegreeTorsionClass_inflation, map_zero]
    change (unramifiedMultiplicativeInflation R K C 2).hom
      ((unramifiedMultiplicativeInvariant R K C).symm 0) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    apply galoisMultiplicativeInflationH2_injective K C E
    rw [map_add, relativeDegreeTorsionClass_inflation, relativeDegreeTorsionClass_inflation,
      relativeDegreeTorsionClass_inflation]
    change (unramifiedMultiplicativeInflation R K C 2).hom
      ((unramifiedMultiplicativeInvariant R K C).symm (x.val + y.val)) = _
    rw [map_add, map_add]

/-- Distinct degree-torsion invariants give distinct actual relative H2 classes. -/
theorem relativeDegreeTorsionHom_injective :
    Function.Injective (relativeDegreeTorsionHom R S K C E) := by
  intro x y h
  have he := congrArg (galoisMultiplicativeInflation K C E 2).hom h
  change (galoisMultiplicativeInflation K C E 2).hom
      (relativeDegreeTorsionClass R S K C E x) =
    (galoisMultiplicativeInflation K C E 2).hom
      (relativeDegreeTorsionClass R S K C E y) at he
  rw [relativeDegreeTorsionClass_inflation, relativeDegreeTorsionClass_inflation] at he
  exact Subtype.ext ((unramifiedMultiplicativeInvariant R K C).symm.injective
    (unramifiedMultiplicativeInflationH2_injective R K C he))

/-- A cyclic subgroup of degree order is embedded in relative multiplicative H2. -/
def relativeLowerBound : ZMod d →+ continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 := by
  let : NeZero d := ⟨Module.finrank_pos.ne'⟩
  exact (relativeDegreeTorsionHom R S K C E).comp (relativeRestrictionKernelEquiv d).toAddMonoidHom

/-- The relative lower bound is an embedding, derived from the arithmetic degree formula. -/
theorem relativeLowerBound_injective : Function.Injective (relativeLowerBound R S K C E) := by
  let : NeZero d := ⟨Module.finrank_pos.ne'⟩
  exact (relativeDegreeTorsionHom_injective R S K C E).comp
    (relativeRestrictionKernelEquiv d).injective

/-- The constructed relative subgroup has exactly the field degree many elements. -/
theorem relativeLowerBound_card_range :
    Nat.card (relativeLowerBound R S K C E).range = d := by
  rw [← Nat.card_congr (AddMonoidHom.ofInjective
    (relativeLowerBound_injective R S K C E)).toEquiv]
  exact Nat.card_zmod d

end LocalClassFieldTheory
