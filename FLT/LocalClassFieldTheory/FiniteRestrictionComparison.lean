/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteContinuousComparison
public import FLT.LocalClassFieldTheory.ContinuousRestriction

/-!
# Finite continuous comparison commutes with restriction

The comparison forgets continuity without changing cochain values. It therefore
intertwines the actual group-and-coefficient maps in every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex groupCohomology

variable {k G H M P : Type} [CommRing k] [Group G] [Group H]
  [AddCommGroup M] [Module k M] [DistribMulAction H M] [SMulCommClass H k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [TopologicalSpace G] [IsTopologicalGroup G] [Finite G] [DiscreteTopology G]
  [TopologicalSpace H] [IsTopologicalGroup H] [Finite H] [DiscreteTopology H]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul H M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k H M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)

/-- Forgetting continuity intertwines actual pullback on cochains. -/
theorem finiteContinuousComplexIso_restriction (f : G →* H) (hf : Continuous f)
    (φ : Rep.res f RM ⟶ RP) :
    continuousRestriction f hf φ ≫ (finiteContinuousComplexIso k G P).hom =
      (finiteContinuousComplexIso k H M).hom ≫ cochainsMap f φ := by
  ext n c
  rfl

/-- Ordinary and continuous restriction agree under the finite comparison isomorphism. -/
theorem finiteContinuousCohomologyIso_restriction (f : G →* H) (hf : Continuous f)
    (φ : Rep.res f RM ⟶ RP) (n : ℕ) :
    homologyMap (continuousRestriction f hf φ) n ≫
        (finiteContinuousCohomologyIso k G P n).hom =
      (finiteContinuousCohomologyIso k H M n).hom ≫ groupCohomology.map f φ n := by
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n ≫ homologyMap _ n
  rw [← homologyMap_comp, ← homologyMap_comp, finiteContinuousComplexIso_restriction]

end LocalClassFieldTheory
