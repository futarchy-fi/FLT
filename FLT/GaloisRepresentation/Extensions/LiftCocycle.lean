/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ChangeSplitting

/-!
# Cocycles obtained by lifting an invariant quotient vector

For an equivariant injection, the difference between a lifted vector and
its translate determines a unique cocycle. This construction uses only
invariance modulo the image and proves the change-of-splitting formula.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G A V : Type*} [Group G] [AddCommGroup A] [AddCommGroup V]
    [DistribMulAction G A] [DistribMulAction G V]
    (i : A →+ V) (hi : Function.Injective i)
    (heq : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (v : V) (hv : ∀ g : G, g • v - v ∈ i.range)

/-- Coefficients of the difference of a lift and its translate. -/
noncomputable def liftCocycle (g : G) : A := Classical.choose (hv g)

omit [DistribMulAction G A] in
/-- The defining difference equation for the lifted cocycle. -/
theorem liftCocycle_spec (g : G) : i (liftCocycle i v hv g) = g • v - v :=
  Classical.choose_spec (hv g)

include hi heq in
/-- Injectivity forces the lifted difference to satisfy the cocycle identity. -/
theorem liftCocycle_isCocycle : groupCohomology.IsCocycle₁ (liftCocycle i v hv) := by
  intro g h
  apply hi
  rw [map_add, heq, liftCocycle_spec, liftCocycle_spec, liftCocycle_spec, mul_smul, smul_sub]
  abel

include hi in
omit [DistribMulAction G A] in
/-- The defining equation uniquely determines the representative. -/
theorem liftCocycle_unique (c : G → A) (hc : ∀ g : G, i (c g) = g • v - v) :
    c = liftCocycle i v hv := by
  funext g
  exact hi ((hc g).trans (liftCocycle_spec i v hv g).symm)

include heq hv in
/-- Changing the lift within its coset preserves quotient invariance. -/
theorem liftCocycle_range_add (a : A) (g : G) :
    g • (v + i a) - (v + i a) ∈ i.range := by
  refine ⟨changeSplitting (liftCocycle i v hv) a g, ?_⟩
  simp only [changeSplitting, map_add, map_sub, heq, liftCocycle_spec, smul_add]
  abel

include hi in
/-- The cocycles from two lifts of the same quotient vector differ by a coboundary. -/
theorem liftCocycle_add (a : A) :
    liftCocycle i (v + i a) (liftCocycle_range_add i heq v hv a) =
      changeSplitting (liftCocycle i v hv) a := by
  symm
  apply liftCocycle_unique i hi
  intro g
  simp only [changeSplitting, map_add, map_sub, heq, liftCocycle_spec, smul_add]
  abel

variable [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace V]
    [IsTopologicalAddGroup V]

omit [DistribMulAction G A] in
/-- An inducing coefficient injection transports continuity of the orbit map
into continuity of the cocycle. -/
theorem continuous_liftCocycle (hiTop : Topology.IsInducing i)
    (hcont : Continuous (fun g : G ↦ g • v)) : Continuous (liftCocycle i v hv) := by
  apply hiTop.continuous_iff.mpr
  have h : i ∘ liftCocycle i v hv = fun g : G ↦ g • v - v :=
    funext (liftCocycle_spec i v hv)
  rw [h]
  exact hcont.sub continuous_const

end GaloisRepresentation.Extensions
