/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SubgroupNormDecomposition
public import FLT.LocalClassFieldTheory.TateInvariantClass
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Deflation at the Tate norm splice

The full norm factors through the subgroup norm and the quotient norm.
Thus the identity on fixed coefficients induces a surjection from the
ambient degree-zero Tate group to the quotient group's Tate group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (M : Rep k G) (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]

local notation "MQ" => M.quotientToInvariants N

/-- Full invariants equal quotient invariants of subgroup invariants. -/
def quotientInvariantEquiv : M.ρ.invariants ≃ₗ[k] (MQ).ρ.invariants where
  toFun x := ⟨⟨x, fun n => x.property n⟩, fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    exact Subtype.ext (x.property g)⟩
  invFun x := ⟨x.val.val, fun g => congrArg Subtype.val (x.property (QuotientGroup.mk' N g))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Full norms become quotient norms under the invariant identification. -/
theorem quotientInvariantEquiv_class_kernel :
    LinearMap.ker (tateInvariantClass M).hom ≤
      LinearMap.ker
        ((tateInvariantClass MQ).hom.comp (quotientInvariantEquiv M N).toLinearMap) := by
  classical
  let : Fintype N := Fintype.ofFinite _
  intro x hx
  obtain ⟨y, hy⟩ := (tateInvariantClass_eq_zero_iff M x).mp hx
  exact (tateInvariantClass_eq_zero_iff MQ _).mpr
    ⟨subgroupNormInvariant M N y, Subtype.ext ((quotientNorm_subgroupNorm M N y).trans hy)⟩

/-- Deflation on the actual degree-zero Tate groups, constructed from the norm factorization. -/
def tateZeroDeflation : tateCohomology M 0 →ₗ[k] tateCohomology MQ 0 :=
  ((LinearMap.ker (tateInvariantClass M).hom).liftQ
    ((tateInvariantClass MQ).hom.comp (quotientInvariantEquiv M N).toLinearMap)
    (quotientInvariantEquiv_class_kernel M N)).comp
      ((tateInvariantClass M).hom.quotKerEquivOfSurjective
        (tateInvariantClass_surjective M)).symm.toLinearMap

/-- Deflation preserves the underlying fixed coefficient of an invariant class. -/
theorem tateZeroDeflation_class (x : M.ρ.invariants) :
    tateZeroDeflation M N (tateInvariantClass M x) =
      tateInvariantClass MQ (quotientInvariantEquiv M N x) := by
  simp only [tateZeroDeflation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- Every quotient invariant class lifts to an ambient invariant class. -/
theorem tateZeroDeflation_surjective : Function.Surjective (tateZeroDeflation M N) := by
  intro a
  obtain ⟨x, rfl⟩ := tateInvariantClass_surjective MQ a
  refine ⟨tateInvariantClass M ((quotientInvariantEquiv M N).symm x), ?_⟩
  rw [tateZeroDeflation_class, LinearEquiv.apply_symm_apply]

/-- An invariant class deflates to zero precisely when it is a quotient norm. -/
theorem tateZeroDeflation_class_eq_zero_iff (x : M.ρ.invariants) :
    tateZeroDeflation M N (tateInvariantClass M x) = 0 ↔
      ∃ y : MQ, (MQ).norm.hom y = (quotientInvariantEquiv M N x).val := by
  rw [tateZeroDeflation_class, tateInvariantClass_eq_zero_iff]

end LocalClassFieldTheory
