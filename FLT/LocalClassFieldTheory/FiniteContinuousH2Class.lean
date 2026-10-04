/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteContinuousComparison
public import FLT.LocalClassFieldTheory.IntegralDegreeTwoComparison

/-!
# Finite comparison on explicit two-cocycles

Forgetting continuity takes the explicit continuous class to the ordinary
class of the same function, without a sign or a change of coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex groupCohomology GaloisRepresentation.Extensions

variable {k G M : Type} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [Finite G] [DiscreteTopology G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

local notation "A" => Rep.of (Representation.ofDistribMulAction k G M)

/-- A continuous two-cocycle gives the ordinary cocycle with identical values. -/
def continuousOrdinaryTwoCocycle (c : C(G × G, M)) (hc : IsCocycle₂ c) :
    cocycles₂ A :=
  ⟨c, (mem_cocycles₂_iff _).mpr hc⟩

/-- Finite continuous comparison preserves the explicit two-cocycle representative. -/
theorem finiteContinuousH2Class (c : C(G × G, M)) (hc : IsCocycle₂ c) :
    (finiteContinuousCohomologyIso k G M 2).hom (integralH2Class c hc) =
      H2π A (continuousOrdinaryTwoCocycle c hc) := by
  unfold integralH2Class
  change (homologyMap (finiteContinuousComplexIso k G M).hom 2).hom
    (cochainHomologyClass _ _ _ _) = _
  rw [cochainHomologyClass_map _ _ _ _ _
    (cochainMap_cycle _ _ _ _ _ (by
      rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
      exact (continuousTwoCochain_cycle_iff (k := k) c).mpr hc))]
  change (π A 2).hom _ = (π A 2).hom _
  congr 1
  exact cocyclesMk₂_eq A (continuousOrdinaryTwoCocycle c hc)

end LocalClassFieldTheory
