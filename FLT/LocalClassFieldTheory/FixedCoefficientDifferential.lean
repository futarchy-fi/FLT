/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FixedCoefficientCochain
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Differential compatibility for invariant-coefficient inflation

Specialize the existing cochain map to the quotient action on invariant
coefficients. Inflation is injective and commutes with the inhomogeneous
differential, so the descended continuous cocycles are finite-stage cocycles.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]

local notation "ρ" => Representation.ofDistribMulAction k G M

/-- Inflation from the quotient's invariant coefficient representation is a cochain map. -/
def invariantCochainInflation (N : Subgroup G) [N.Normal] :
    inhomogeneousCochains (Rep.of ((ρ).quotientToInvariants N)) ⟶
      inhomogeneousCochains (Rep.of ρ) :=
  groupCohomology.cochainsMap (QuotientGroup.mk' N)
    (Rep.ofHom ((ρ).quotientToInvariants_lift N))

/-- Inflation evaluates by lifting the arguments and including the invariant values. -/
theorem invariantCochainInflation_apply (N : Subgroup G) [N.Normal] (n : ℕ)
    (d : (Fin n → G ⧸ N) → (Representation.invariants ((ρ).comp N.subtype))) (x : Fin n → G) :
    ((invariantCochainInflation k G M N).f n).hom d x =
      (d (fun i => QuotientGroup.mk' N (x i)) : M) := rfl

/-- Surjectivity on tuples and injectivity of coefficient inclusion make inflation injective. -/
theorem invariantCochainInflation_injective (N : Subgroup G) [N.Normal] (n : ℕ) :
    Function.Injective ((invariantCochainInflation k G M N).f n).hom := by
  intro c d h
  funext y
  choose x hx using fun i => QuotientGroup.mk'_surjective N (y i)
  apply Subtype.ext
  have he := congrFun h x
  change (c (fun i => QuotientGroup.mk' N (x i)) : M) =
    (d (fun i => QuotientGroup.mk' N (x i)) : M) at he
  simpa only [funext hx] using he

/-- The actual finite-stage differential commutes with inflation. -/
theorem invariantCochainInflation_d (N : Subgroup G) [N.Normal] (n : ℕ)
    (d : (Fin n → G ⧸ N) → (Representation.invariants ((ρ).comp N.subtype))) :
    ((invariantCochainInflation k G M N).f (n + 1)).hom
        ((inhomogeneousCochains.d (Rep.of ((ρ).quotientToInvariants N)) n).hom d) =
      (inhomogeneousCochains.d (Rep.of ρ) n).hom
        (((invariantCochainInflation k G M N).f n).hom d) := by
  have h := (invariantCochainInflation k G M N).comm n (n + 1)
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def] at h
  exact (congrArg (fun f => f.hom d) h).symm

/-- A cochain in invariant coefficients is a cocycle exactly when its inflation is. -/
theorem invariantCochainInflation_cocycle_iff (N : Subgroup G) [N.Normal] (n : ℕ)
    (d : (Fin n → G ⧸ N) → (Representation.invariants ((ρ).comp N.subtype))) :
    (inhomogeneousCochains.d (Rep.of ((ρ).quotientToInvariants N)) n).hom d = 0 ↔
      (inhomogeneousCochains.d (Rep.of ρ) n).hom
        (((invariantCochainInflation k G M N).f n).hom d) = 0 := by
  rw [← invariantCochainInflation_d, ← map_zero ((invariantCochainInflation k G M N).f
    (n + 1)).hom, (invariantCochainInflation_injective k G M N (n + 1)).eq_iff]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- Every continuous inhomogeneous cocycle descends to a finite quotient's actual cocycle. -/
theorem exists_descended_invariant_cocycle (n : ℕ) (c : C(Fin n → G, M))
    (hc : (inhomogeneousCochains.d (Rep.of ρ) n).hom c = 0) :
    ∃ N : OpenNormalSubgroup G, Finite (G ⧸ N.toSubgroup) ∧
      ∃ d : C(Fin n → G ⧸ N.toSubgroup,
          Representation.invariants ((ρ).comp N.toSubgroup.subtype)),
        (∀ x : Fin n → G, (d (fun i => QuotientGroup.mk' N.toSubgroup (x i)) : M) = c x) ∧
        (inhomogeneousCochains.d (Rep.of ((ρ).quotientToInvariants N.toSubgroup)) n).hom d = 0 := by
  obtain ⟨N, hN, d, hd⟩ := exists_descended_invariant_cochain k G M c
  refine ⟨N, hN, d, hd, ?_⟩
  apply (invariantCochainInflation_cocycle_iff k G M N.toSubgroup n d).mpr
  have he : ((invariantCochainInflation k G M N.toSubgroup).f n).hom d = c := funext hd
  rwa [he]

end LocalClassFieldTheory
