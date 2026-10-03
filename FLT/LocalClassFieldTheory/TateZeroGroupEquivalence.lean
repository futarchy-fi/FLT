/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateGroupEquivalence
public import FLT.LocalClassFieldTheory.TateInvariantClass
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Group equivalence on invariant Tate classes

Reindexing the norm by a group equivalence allows coefficient morphisms to
act on the actual degree-zero Tate groups. Injective coefficient morphisms
reflect zero classes when they are also surjective.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G H : Type} [CommRing k] [Group G] [Group H] [Fintype G] [Fintype H]
  (M : Rep k G) (N : Rep k H) (e : H ≃* G) (f : Rep.res e.toMonoidHom M ⟶ N)

/-- Reindex a fixed coefficient and apply the coefficient morphism. -/
def groupEquivalenceInvariant : M.ρ.invariants →ₗ[k] N.ρ.invariants where
  toFun x := ⟨f.hom x, fun h => by
    rw [← Rep.hom_comm_apply]
    exact congrArg f.hom (x.property (e h))⟩
  map_add' _ _ := Subtype.ext (map_add f.hom _ _)
  map_smul' _ _ := Subtype.ext (map_smul f.hom _ _)

/-- A coefficient morphism carries the reindexed norm to the target norm. -/
theorem groupEquivalence_norm_map (x : M) :
    N.norm.hom (f.hom x) = f.hom (M.norm.hom x) := by
  rw [← groupEquivalence_norm M e]
  change (∑ h : H, N.ρ h) (f.hom x) = f.hom ((∑ h : H, M.ρ (e h)) x)
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro h _
  exact (Rep.hom_comm_apply f h x).symm

/-- The transported invariant class vanishes on the original norm kernel. -/
theorem groupEquivalenceInvariant_class_kernel :
    LinearMap.ker (tateInvariantClass M).hom ≤
      LinearMap.ker ((tateInvariantClass N).hom.comp (groupEquivalenceInvariant M N e f)) := by
  intro x hx
  obtain ⟨y, hy⟩ := (tateInvariantClass_eq_zero_iff M x).mp hx
  exact (tateInvariantClass_eq_zero_iff N _).mpr
    ⟨f.hom y, (groupEquivalence_norm_map M N e f y).trans (congrArg f.hom hy)⟩

/-- Group reindexing with coefficients on the actual degree-zero Tate groups. -/
def tateZeroGroupEquivalence : tateCohomology M 0 →ₗ[k] tateCohomology N 0 :=
  ((LinearMap.ker (tateInvariantClass M).hom).liftQ
    ((tateInvariantClass N).hom.comp (groupEquivalenceInvariant M N e f))
    (groupEquivalenceInvariant_class_kernel M N e f)).comp
      ((tateInvariantClass M).hom.quotKerEquivOfSurjective
        (tateInvariantClass_surjective M)).symm.toLinearMap

/-- Group reindexing acts on an invariant class by the coefficient morphism. -/
theorem tateZeroGroupEquivalence_class (x : M.ρ.invariants) :
    tateZeroGroupEquivalence M N e f (tateInvariantClass M x) =
      tateInvariantClass N (groupEquivalenceInvariant M N e f x) := by
  simp only [tateZeroGroupEquivalence, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- Bijective coefficient transport reflects equality of actual Tate classes. -/
theorem tateZeroGroupEquivalence_injective (hf : Function.Bijective f.hom) :
    Function.Injective (tateZeroGroupEquivalence M N e f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨x, rfl⟩ := tateInvariantClass_surjective M a
  rw [tateZeroGroupEquivalence_class] at ha
  obtain ⟨y, hy⟩ := (tateInvariantClass_eq_zero_iff N _).mp ha
  obtain ⟨z, rfl⟩ := hf.2 y
  apply (tateInvariantClass_eq_zero_iff M x).mpr
  refine ⟨z, hf.1 ?_⟩
  exact (groupEquivalence_norm_map M N e f z).symm.trans hy

end LocalClassFieldTheory
