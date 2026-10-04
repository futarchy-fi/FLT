/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupRestrictionNorm
public import FLT.LocalClassFieldTheory.TateZeroTransfer

/-!
# Restriction in Tate degree zero

The invariant inclusion descends to the actual Tate groups by the right-coset
norm identity. Corestriction after restriction is multiplication by the index.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (M : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

local notation "MH" => Rep.res H.subtype M

omit [Fintype (G ⧸ H)] in
/-- Restriction on invariant classes kills the kernel of the ambient class map. -/
theorem restrictInvariant_class_kernel :
    LinearMap.ker (tateInvariantClass M).hom ≤
      LinearMap.ker ((tateInvariantClass MH).hom.comp (restrictInvariant M H)) := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  intro x hx
  obtain ⟨y, hy⟩ := (tateInvariantClass_eq_zero_iff M x).mp hx
  apply (tateInvariantClass_eq_zero_iff MH _).mpr
  exact ⟨restrictionZero M H y, (norm_sum_right_cosets M H y).trans hy⟩

/-- Restriction on the actual degree-zero Tate group. -/
def tateZeroRestriction : tateCohomology M 0 →ₗ[k] tateCohomology MH 0 :=
  ((LinearMap.ker (tateInvariantClass M).hom).liftQ
    ((tateInvariantClass MH).hom.comp (restrictInvariant M H))
    (restrictInvariant_class_kernel M H)).comp
      ((tateInvariantClass M).hom.quotKerEquivOfSurjective
        (tateInvariantClass_surjective M)).symm.toLinearMap

omit [Fintype (G ⧸ H)] in
/-- Restriction sends an invariant class to the class of the same coefficient. -/
theorem tateZeroRestriction_class (x : M.ρ.invariants) :
    tateZeroRestriction M H (tateInvariantClass M x) =
      tateInvariantClass MH (restrictInvariant M H x) := by
  simp only [tateZeroRestriction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The restriction-corestriction degree formula on the actual Tate group. -/
theorem tateZeroCorestriction_restriction (a : tateCohomology M 0) :
    tateZeroCorestriction M H (tateZeroRestriction M H a) =
      Fintype.card (G ⧸ H) • a := by
  obtain ⟨x, rfl⟩ := tateInvariantClass_surjective M a
  rw [tateZeroRestriction_class, tateZeroCorestriction_class,
    transferInvariant_restrictInvariant, map_nsmul]

omit [Fintype (G ⧸ H)] in
/-- The invariant-class formula uniquely determines restriction. -/
theorem tateZeroRestriction_unique
    (f : tateCohomology M 0 →ₗ[k] tateCohomology MH 0)
    (hf : ∀ x, f (tateInvariantClass M x) =
      tateInvariantClass MH (restrictInvariant M H x)) : f = tateZeroRestriction M H := by
  ext a
  obtain ⟨x, rfl⟩ := tateInvariantClass_surjective M a
  exact (hf x).trans (tateZeroRestriction_class M H x).symm

end LocalClassFieldTheory
