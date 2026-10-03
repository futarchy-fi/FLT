/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.InvariantRestriction

/-!
# Surjectivity and kernel of absolute restriction

Divisibility of Q/Z and the proved degree formula give surjectivity of
actual restriction. Its kernel is exactly the degree-torsion subgroup.
These are prerequisites for comparison with corestriction.
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
  (E : IntermediateField K C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S C] [IsScalarTower R S E]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

attribute [local instance] relativeBaseTower

variable [FiniteDimensional K E] [CharZero C]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p] [CharP (ResidueField S) p]

/-- Multiplication by a nonzero natural number is onto Q/Z. -/
theorem rationalCircle_nsmul_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x : AddCircle (1 : ℚ) => n • x) := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨((q / n : ℚ) : AddCircle (1 : ℚ)), ?_⟩
  change n • ((q / n : ℚ) : AddCircle (1 : ℚ)) = _
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  field_simp

include R S p in
/-- Actual absolute restriction is surjective for a finite local extension. -/
theorem absoluteRestrictionH2_surjective :
    Function.Surjective (absoluteRestriction K C E 2).hom := by
  intro y
  obtain ⟨z, hz⟩ := rationalCircle_nsmul_surjective (Module.finrank K E)
    Module.finrank_pos.ne' (absoluteInvariant S E C p y)
  refine ⟨(absoluteInvariant R K C p).symm z, ?_⟩
  apply (absoluteInvariant S E C p).injective
  rw [absoluteInvariant_restriction R S K C E p, AddEquiv.apply_symm_apply]
  exact hz

include S in
/-- Restriction kills exactly the classes whose invariant is annihilated by the degree. -/
theorem absoluteRestrictionH2_eq_zero_iff
    (x : continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2) :
    (absoluteRestriction K C E 2).hom x = 0 ↔
      Module.finrank K E • absoluteInvariant R K C p x = 0 := by
  rw [← absoluteInvariant_restriction R S K C E p]
  exact (map_eq_zero_iff (absoluteInvariant S E C p)
    (absoluteInvariant S E C p).injective).symm

end LocalClassFieldTheory
