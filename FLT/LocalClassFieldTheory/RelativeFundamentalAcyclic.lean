/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalSubgroup
public import FLT.LocalClassFieldTheory.FiniteTateVanishing

/-!
# All-degree vanishing of the local fundamental extension

Apply the finite-group adjacent criterion to the proved arithmetic vanishing
on every subgroup of the original finite Galois group.
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
/-- The local fundamental extension is Tate acyclic on every subgroup. -/
theorem relativeFundamentalExtension_allSubgroup_isZero
    (H : Subgroup Gal(F/K)) [Fintype H] (n : ℤ) :
    Limits.IsZero (tateCohomology
      (Rep.res H.subtype (relativeFundamentalExtension R S K C F)) n) := by
  apply finite_subgroup_tate_isZero_of_adjacent
      (relativeFundamentalExtension R S K C F) _ _ n H
  · intro J _
    exact relativeFundamentalExtension_subgroup_isZero R S K C F p J 0 (Or.inl rfl)
  · intro J _
    exact relativeFundamentalExtension_subgroup_isZero R S K C F p J 1 (Or.inr rfl)

include p in
/-- The actual middle term of the local fundamental two-extension is Tate acyclic. -/
theorem relativeFundamentalExtension_all_isZero (n : ℤ) :
    Limits.IsZero (tateCohomology (relativeFundamentalExtension R S K C F) n) := by
  apply SubgroupTateVanishing.self
  intro H _
  exact relativeFundamentalExtension_allSubgroup_isZero R S K C F p H n

end LocalClassFieldTheory
