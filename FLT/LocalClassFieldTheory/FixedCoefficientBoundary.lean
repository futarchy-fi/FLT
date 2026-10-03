/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FixedCoefficientDifferential

/-!
# Common-stage descent of continuous boundaries

Descend the bounding cochain first. Its finite differential supplies the
boundary at the same stage, with the same invariant coefficient module.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

local notation "ρ" => Representation.ofDistribMulAction k G M

/-- A continuous boundary and its bounding cochain descend together, and the
finite-stage differential equation holds in the actual invariant coefficients. -/
theorem exists_descended_invariant_boundary (n : ℕ) (b : C(Fin n → G, M))
    (c : C(Fin (n + 1) → G, M))
    (hbc : (inhomogeneousCochains.d (Rep.of ρ) n).hom b = c) :
    ∃ N : OpenNormalSubgroup G, Finite (G ⧸ N.toSubgroup) ∧
      ∃ bN : C(Fin n → G ⧸ N.toSubgroup,
          Representation.invariants ((ρ).comp N.toSubgroup.subtype)),
      ∃ cN : C(Fin (n + 1) → G ⧸ N.toSubgroup,
          Representation.invariants ((ρ).comp N.toSubgroup.subtype)),
        (∀ x, (bN (fun i => QuotientGroup.mk' N.toSubgroup (x i)) : M) = b x) ∧
        (∀ x, (cN (fun i => QuotientGroup.mk' N.toSubgroup (x i)) : M) = c x) ∧
        (inhomogeneousCochains.d (Rep.of ((ρ).quotientToInvariants N.toSubgroup)) n).hom
          bN = cN := by
  obtain ⟨N, hN, bN, hb⟩ := exists_descended_invariant_cochain k G M b
  let : DiscreteTopology (G ⧸ N.toSubgroup) := QuotientGroup.discreteTopology N.isOpen
  let cN : C(Fin (n + 1) → G ⧸ N.toSubgroup,
      Representation.invariants ((ρ).comp N.toSubgroup.subtype)) :=
    ⟨(inhomogeneousCochains.d (Rep.of ((ρ).quotientToInvariants N.toSubgroup)) n).hom bN,
      continuous_of_discreteTopology⟩
  refine ⟨N, hN, bN, cN, hb, ?_, rfl⟩
  have he : ((invariantCochainInflation k G M N.toSubgroup).f n).hom bN = b := funext hb
  have hd := invariantCochainInflation_d k G M N.toSubgroup n bN
  rw [he, hbc] at hd
  exact fun x => congrFun hd x

end LocalClassFieldTheory
