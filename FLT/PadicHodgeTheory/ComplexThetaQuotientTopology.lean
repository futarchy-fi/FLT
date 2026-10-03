/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicQuotientComplete
public import FLT.PadicHodgeTheory.ComplexThetaQuotientSeparated

/-! # Compatible complete p-adic topologies on integral theta quotients

The topology instances are scoped: opening `PadicHodgeTheory` chooses the
p-adic topology here, without imposing it on all Witt vectors globally.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The p-adic topology on the actual A_inf. -/
scoped instance complexAinfWithIdeal : WithIdeal (Ainf p) := ⟨Ideal.span {(p : Ainf p)}⟩

/-- Each integral theta quotient carries its p-adic coefficient topology. -/
scoped instance complexIntegralThetaQuotientWithIdeal (n : ℕ) :
    WithIdeal (ComplexIntegralThetaQuotient p n) :=
  ⟨Ideal.span {(p : ComplexIntegralThetaQuotient p n)}⟩

/-- Choose the adic topology explicitly, ahead of the generic quotient topology. -/
scoped instance complexIntegralThetaQuotientTopology (n : ℕ) :
    TopologicalSpace (ComplexIntegralThetaQuotient p n) :=
  (Ideal.span {(p : ComplexIntegralThetaQuotient p n)}).adicTopology

/-- Precompleteness descends from A_inf, and separatedness was proved independently. -/
instance complexIntegralThetaQuotient_isAdicComplete (n : ℕ) :
    IsAdicComplete (Ideal.span {(p : ComplexIntegralThetaQuotient p n)})
      (ComplexIntegralThetaQuotient p n) where
  toIsPrecomplete := by
    have h := adicPrecomplete_quotient_map (Ideal.span {(p : Ainf p)})
      (RingHom.ker (complexTheta p) ^ n)
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h

/-- The coefficient topology is Hausdorff for every n, including zero. -/
scoped instance complexIntegralThetaQuotient_t2Space (n : ℕ) :
    T2Space (ComplexIntegralThetaQuotient p n) :=
  (IsAdic.isHausdorff_iff (I := Ideal.span {(p : ComplexIntegralThetaQuotient p n)})
    rfl).mp inferInstance

/-- Every integral theta quotient is complete for this coefficient topology. -/
scoped instance complexIntegralThetaQuotient_completeSpace (n : ℕ) :
    CompleteSpace (ComplexIntegralThetaQuotient p n) :=
  (IsAdic.isPrecomplete_iff (I := Ideal.span {(p : ComplexIntegralThetaQuotient p n)})
    rfl).mp inferInstance

/-- The actual quotient map is uniformly continuous for p-adic topologies. -/
theorem complexIntegralThetaQuotient_mk_uniformContinuous (n : ℕ) :
    UniformContinuous (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ n)) := by
  apply WithIdeal.uniformContinuous_of_map_le
  change (Ideal.span {(p : Ainf p)}).map _ ≤
    Ideal.span {(p : ComplexIntegralThetaQuotient p n)}
  simp only [Ideal.map_span, Set.image_singleton, map_natCast, le_refl]

/-- The canonical transition maps are uniformly continuous for the same topologies. -/
theorem complexIntegralThetaQuotient_transition_uniformContinuous {m n : ℕ} (h : n ≤ m) :
    UniformContinuous (Ideal.Quotient.factorPow (RingHom.ker (complexTheta p)) h) := by
  apply WithIdeal.uniformContinuous_of_map_le
  change (Ideal.span {(p : ComplexIntegralThetaQuotient p m)}).map _ ≤
    Ideal.span {(p : ComplexIntegralThetaQuotient p n)}
  simp only [Ideal.map_span, Set.image_singleton, map_natCast, le_refl]

/-- Powers of p actually tend to zero in each coefficient topology. -/
theorem complexIntegralThetaQuotient_prime_pow_tendsto (n : ℕ) :
    Filter.Tendsto (fun k : ℕ ↦ (p : ComplexIntegralThetaQuotient p n) ^ k)
      Filter.atTop (nhds 0) :=
  WithIdeal.isTopologicallyNilpotent_of_mem (R := ComplexIntegralThetaQuotient p n)
    (Ideal.subset_span (Set.mem_singleton _))

end PadicHodgeTheory
