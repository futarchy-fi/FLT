/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteUnitInvariants
public import FLT.LocalClassFieldTheory.SubgroupTransferNorm
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Fixed-field norms and coset transfer

For a normal subgroup of a finite Galois group, its fixed-field norm is
exactly the coset transfer on fixed units.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L] (H : Subgroup Gal(L/K))

local notation "E" => IntermediateField.fixedField H
local notation "M" => Rep.ofAlgebraAutOnUnits K L

/-- Units of the fixed field give subgroup-invariant units in the ambient field. -/
def fixedUnitInvariantInclusion : Additive (E)ˣ →ₗ[ℤ] (Rep.res H.subtype M).ρ.invariants :=
  (Units.map (algebraMap E L).toMonoidHom).toAdditive.toIntLinearMap.codRestrict _ fun u g => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (Additive.toMul u : Eˣ).val.property g

variable [H.Normal] [Fintype (Gal(L/K) ⧸ H)]

/-- The algebraic norm from the fixed field is the product over the actual coset representatives. -/
theorem normalFixedField_norm (x : E) :
    algebraMap K L (Algebra.norm K x) = ∏ q : Gal(L/K) ⧸ H, q.out (x : L) := by
  classical
  rw [IsScalarTower.algebraMap_apply K E L, Algebra.norm_eq_prod_automorphisms, map_prod]
  have hp := Equiv.prod_comp (IsGalois.normalAutEquivQuotient H).toEquiv
    (fun g : Gal(E/K) => algebraMap E L (g x))
  rw [← hp]
  apply Finset.prod_congr rfl
  intro q _
  have he : IsGalois.normalAutEquivQuotient H q =
      AlgEquiv.restrictNormalHom E q.out := by
    exact (congrArg (IsGalois.normalAutEquivQuotient H)
      (QuotientGroup.out_eq' q)).symm
  change algebraMap E L ((IsGalois.normalAutEquivQuotient H q) x) = _
  rw [he]
  exact AlgEquiv.restrictNormal_commutes q.out E x

/-- Coset transfer of a fixed-field unit is the included field norm. -/
theorem transferInvariant_fixedUnit_norm (v : Eˣ) :
    transferInvariant M H (fixedUnitInvariantInclusion K L H (Additive.ofMul v)) =
      finiteUnitInvariantInclusion K L (Additive.ofMul (Units.map (Algebra.norm K) v)) := by
  classical
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  change ((Additive.toMul (transferZero M H _)) : Lˣ).val =
    algebraMap K L (Algebra.norm K (v : E))
  rw [transferZero_apply, toMul_sum, Units.coe_prod]
  change (∏ q : Gal(L/K) ⧸ H, q.out ((v : E) : L)) = _
  exact (normalFixedField_norm K L H (v : E)).symm

end LocalClassFieldTheory
