/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousRestrictionColimit
public import FLT.LocalClassFieldTheory.ContinuousCohomologyColimit

/-!
# Restriction naturality on continuous cohomology

The index functor pulls back open normal subgroups. Its quotient cochain maps
induce the actual restriction map under the proved colimit comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits HomologicalComplex

variable {k G H M P : Type u} [CommRing k] [Group G] [Group H]
  [AddCommGroup M] [Module k M] [DistribMulAction H M] [SMulCommClass H k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul H M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k H M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)

/-- Quotient restriction induces a natural transformation on finite-stage cohomology. -/
def restrictionStageCohomologyNat (f : G →* H) (hf : Continuous f)
    (φ : Rep.res f RM ⟶ RP) (n : ℕ) :
    invariantStageCohomologyDiagram k H M n ⟶
      restrictionStageFunctor f hf ⋙ invariantStageCohomologyDiagram k G P n :=
  Functor.whiskerRight (restrictionStageNat f hf φ)
    (homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n)

/-- The cohomology colimit comparison intertwines finite-stage and continuous restriction. -/
theorem continuousRestriction_cohomologyColimit (f : G →* H) (hf : Continuous f)
    (φ : Rep.res f RM ⟶ RP) (n : ℕ) :
    colimMap (restrictionStageCohomologyNat f hf φ n) ≫
        colimit.pre (invariantStageCohomologyDiagram k G P n) (restrictionStageFunctor f hf) ≫
        (continuousCohomologyColimitIso k G P n).hom =
      (continuousCohomologyColimitIso k H M n).hom ≫
        homologyMap (continuousRestriction f hf φ) n := by
  apply colimit.hom_ext
  intro N
  rw [ι_colimMap_assoc, colimit.ι_pre_assoc]
  change (restrictionStageCohomologyNat f hf φ n).app N ≫
    colimit.ι (invariantStageCohomologyDiagram k G P n) ((restrictionStageFunctor f hf).obj N) ≫
      ((colimit.isColimit _).coconePointUniqueUpToIso (continuousCohomologyIsColimit k G P n)).hom =
    (colimit.ι _ N ≫ ((colimit.isColimit _).coconePointUniqueUpToIso
      (continuousCohomologyIsColimit k H M n)).hom) ≫ homologyMap (continuousRestriction f hf φ) n
  rw [colimit.comp_coconePointUniqueUpToIso_hom,
    colimit.comp_coconePointUniqueUpToIso_hom]
  exact (homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun g => homologyMap g n)
      (continuousRestriction_inflation f hf φ (OrderDual.ofDual N))).trans
        (homologyMap_comp _ _ n))

end LocalClassFieldTheory
