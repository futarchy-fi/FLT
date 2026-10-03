/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupTransferNorm
public import FLT.LocalClassFieldTheory.TateInvariantClass
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Subgroup corestriction in Tate degree zero

The actual coset sum on invariants descends through the proved norm kernel.
The resulting map acts on the existing Tate cohomology objects.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (M : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

local notation "MH" => Rep.res H.subtype M

/-- The coset sum on invariant classes kills the kernel of the subgroup class map. -/
theorem transferInvariant_class_kernel :
    LinearMap.ker (tateInvariantClass MH).hom ≤
      LinearMap.ker ((tateInvariantClass M).hom.comp (transferInvariant M H)) := by
  intro x hx
  obtain ⟨y, hy⟩ := (tateInvariantClass_eq_zero_iff MH x).mp hx
  apply (tateInvariantClass_eq_zero_iff M _).mpr
  refine ⟨y, ?_⟩
  change M.norm.hom y = transferZero M H (x : M)
  rw [← hy, transferZero_norm]

/-- Corestriction on actual degree-zero Tate cohomology. -/
def tateZeroCorestriction : tateCohomology MH 0 →ₗ[k] tateCohomology M 0 :=
  ((LinearMap.ker (tateInvariantClass MH).hom).liftQ
    ((tateInvariantClass M).hom.comp (transferInvariant M H))
    (transferInvariant_class_kernel M H)).comp
      ((tateInvariantClass MH).hom.quotKerEquivOfSurjective
        (tateInvariantClass_surjective MH)).symm.toLinearMap

/-- Corestriction carries an invariant class to its actual coset-norm class. -/
theorem tateZeroCorestriction_class (x : (MH).ρ.invariants) :
    tateZeroCorestriction M H (tateInvariantClass MH x) =
      tateInvariantClass M (transferInvariant M H x) := by
  simp only [tateZeroCorestriction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The invariant-class formula uniquely determines corestriction. -/
theorem tateZeroCorestriction_unique
    (f : tateCohomology MH 0 →ₗ[k] tateCohomology M 0)
    (hf : ∀ x, f (tateInvariantClass MH x) =
      tateInvariantClass M (transferInvariant M H x)) : f = tateZeroCorestriction M H := by
  ext a
  obtain ⟨x, rfl⟩ := tateInvariantClass_surjective MH a
  exact (hf x).trans (tateZeroCorestriction_class M H x).symm

end LocalClassFieldTheory
