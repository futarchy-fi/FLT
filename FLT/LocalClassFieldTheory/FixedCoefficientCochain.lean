/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DescendedCochain
public import Mathlib.RepresentationTheory.Invariants

/-!
# Descended cochains with actual invariant coefficients

The values of W16's finite quotient cochain lie in the invariant submodule.
Mathlib's quotient representation supplies the action on that module; no
quotient-action or equivariance bridge is assumed.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]

local notation "ρ" => Representation.ofDistribMulAction k G M

/-- The invariant coefficient module carries the quotient action agreeing with the original one. -/
theorem quotientToInvariants_apply (N : Subgroup G) [N.Normal] (g : G)
    (x : (Representation.invariants ((ρ).comp N.subtype))) :
    ((ρ).quotientToInvariants N (QuotientGroup.mk' N g) x : M) = g • (x : M) := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- A continuous cochain descends to a finite quotient with values in its actual
invariant coefficient module. -/
theorem exists_descended_invariant_cochain {ι : Type*} [Finite ι] (c : C(ι → G, M)) :
    ∃ N : OpenNormalSubgroup G, Finite (G ⧸ N.toSubgroup) ∧
      ∃ d : C(ι → G ⧸ N.toSubgroup, (Representation.invariants ((ρ).comp N.toSubgroup.subtype))),
        ∀ x : ι → G, (d (fun i => QuotientGroup.mk' N.toSubgroup (x i)) : M) = c x := by
  obtain ⟨N, hN, d, hd, hf⟩ := exists_descended_cochain c
  let d' : C(ι → G ⧸ N.toSubgroup, (Representation.invariants ((ρ).comp N.toSubgroup.subtype))) :=
    ⟨fun y => ⟨d y, fun g => hf g.val g.property y⟩, d.continuous.subtype_mk _⟩
  exact ⟨N, hN, d', hd⟩

end LocalClassFieldTheory
