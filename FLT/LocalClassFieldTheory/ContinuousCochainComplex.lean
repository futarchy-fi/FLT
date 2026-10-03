/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FixedCoefficientBoundary

/-!
# The continuous inhomogeneous cochain complex

Continuity defines a submodule in each degree. Finite descent and inflation
prove that the ordinary inhomogeneous differential preserves this submodule.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [DiscreteTopology M]

local notation "ρ" => Representation.ofDistribMulAction k G M

/-- Continuous cochains, as a submodule of all inhomogeneous cochains. -/
def continuousCochainModule (n : ℕ) : Submodule k ((Fin n → G) → M) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' a _ hf := (continuous_of_discreteTopology (f := fun x : M => a • x)).comp hf

omit [DiscreteTopology M] in
/-- Every cochain on an open quotient inflates to a continuous cochain. -/
theorem continuous_invariantCochainInflation (N : OpenNormalSubgroup G) (n : ℕ)
    (c : (Fin n → G ⧸ N.toSubgroup) →
      Representation.invariants ((ρ).comp N.toSubgroup.subtype)) :
    Continuous (((invariantCochainInflation k G M N.toSubgroup).f n).hom c) := by
  let : DiscreteTopology (G ⧸ N.toSubgroup) := QuotientGroup.discreteTopology N.isOpen
  exact (continuous_subtype_val.comp (continuous_of_discreteTopology (f := c))).comp
    (continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i))

variable [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul G M]

/-- The inhomogeneous differential preserves continuity. -/
theorem continuous_inhomogeneous_d (n : ℕ) (c : C(Fin n → G, M)) :
    Continuous ((inhomogeneousCochains.d (Rep.of ρ) n).hom c) := by
  obtain ⟨N, _, d, hd⟩ := exists_descended_invariant_cochain k G M c
  have he : ((invariantCochainInflation k G M N.toSubgroup).f n).hom d = c := funext hd
  rw [← he, ← invariantCochainInflation_d]
  exact continuous_invariantCochainInflation k G M N (n + 1) _

/-- The differential restricted to continuous cochains. -/
def continuousCochainD (n : ℕ) :
    continuousCochainModule k G M n →ₗ[k] continuousCochainModule k G M (n + 1) :=
  ((inhomogeneousCochains.d (Rep.of ρ) n).hom.comp
    (continuousCochainModule k G M n).subtype).codRestrict _
      (fun c => continuous_inhomogeneous_d k G M n ⟨c.val, c.property⟩)

/-- Continuous differentials square to zero because the algebraic ones do. -/
theorem continuousCochainD_comp (n : ℕ) :
    (continuousCochainD k G M (n + 1)).comp (continuousCochainD k G M n) = 0 := by
  ext c x
  exact congrArg (fun f => f.hom c.val x)
    (inhomogeneousCochains.d_comp_d n (Rep.of ρ))

/-- The continuous inhomogeneous complex, with the ordinary differential. -/
def continuousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (continuousCochainModule k G M n))
    (fun n => ModuleCat.ofHom (continuousCochainD k G M n))
    (fun n => ModuleCat.hom_ext (continuousCochainD_comp k G M n))

/-- Forget continuity, retaining the actual algebraic cochain. -/
def continuousCochainsInclusion :
    continuousCochains k G M ⟶ inhomogeneousCochains (Rep.of ρ) :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (continuousCochainModule k G M n).subtype)
    (fun n => by
      ext c x
      simp only [continuousCochains, CochainComplex.of_d]
      rfl)

end LocalClassFieldTheory
