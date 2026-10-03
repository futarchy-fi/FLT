/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalSubgroup
public import FLT.LocalClassFieldTheory.CyclicTateVanishing

/-!
# All-degree vanishing on cyclic local subgroups

Apply the proved cyclic criterion to the arbitrary-subgroup adjacent vanishing
of the original local fundamental extension. No vanishing or equivalence is
supplied by the caller.
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

include p in
/-- The original fundamental extension is Tate acyclic on every cyclic subgroup. -/
theorem relativeFundamentalExtension_cyclicSubgroup_isZero
    (H : Subgroup Gal(F/K)) [Fintype H] [IsCyclic H] (n : ℤ) :
    Limits.IsZero (tateCohomology
      (Rep.res H.subtype (relativeFundamentalExtension R S K C F)) n) :=
  cyclic_tate_isZero_of_adjacent _
    (relativeFundamentalExtension_subgroup_isZero R S K C F p H 0 (Or.inl rfl))
    (relativeFundamentalExtension_subgroup_isZero R S K C F p H 1 (Or.inr rfl)) n

end LocalClassFieldTheory
