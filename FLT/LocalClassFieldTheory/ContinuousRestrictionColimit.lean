/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousRestriction
public import FLT.LocalClassFieldTheory.ContinuousCochainColimit

/-!
# Restriction naturality of the finite-stage colimit

The index functor pulls back open normal subgroups. Its quotient cochain maps
induce the actual restriction map under the proved colimit comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits

variable {k G H M P : Type u} [CommRing k] [Group G] [Group H]
  [AddCommGroup M] [Module k M] [DistribMulAction H M] [SMulCommClass H k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul H M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k H M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)

/-- Pulling back subgroups preserves refinement, hence defines an index functor. -/
def restrictionStageFunctor (f : G →* H) (hf : Continuous f) :
    (OpenNormalSubgroup H)ᵒᵈ ⥤ (OpenNormalSubgroup G)ᵒᵈ where
  obj N := restrictionStage f hf (OrderDual.ofDual N)
  map {N P} g := homOfLE (fun x hx => (leOfHom g) hx)

/-- Restriction of quotient cochains is natural under finite-stage refinement. -/
def restrictionStageNat (f : G →* H) (hf : Continuous f) (φ : Rep.res f RM ⟶ RP) :
    invariantStageDiagram k H M ⟶ restrictionStageFunctor f hf ⋙ invariantStageDiagram k G P where
  app N := restrictionStageMap f hf φ (OrderDual.ofDual N)
  naturality N N' g := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply continuousStageInflation_injective k G P (restrictionStage f hf N') n
    apply Subtype.ext
    funext x
    rfl

/-- The colimit restriction is the actual continuous restriction map. -/
theorem continuousRestriction_colimit (f : G →* H) (hf : Continuous f)
    (φ : Rep.res f RM ⟶ RP) :
    colimMap (restrictionStageNat f hf φ) ≫
        colimit.pre (invariantStageDiagram k G P) (restrictionStageFunctor f hf) ≫
        (continuousCochainsColimitIso k G P).hom =
      (continuousCochainsColimitIso k H M).hom ≫ continuousRestriction f hf φ := by
  apply colimit.hom_ext
  intro N
  rw [ι_colimMap_assoc, colimit.ι_pre_assoc]
  change (restrictionStageNat f hf φ).app N ≫
    colimit.ι (invariantStageDiagram k G P) ((restrictionStageFunctor f hf).obj N) ≫
      ((colimit.isColimit _).coconePointUniqueUpToIso (continuousCochainsIsColimit k G P)).hom =
    (colimit.ι _ N ≫ ((colimit.isColimit _).coconePointUniqueUpToIso
      (continuousCochainsIsColimit k H M)).hom) ≫ continuousRestriction f hf φ
  rw [colimit.comp_coconePointUniqueUpToIso_hom,
    colimit.comp_coconePointUniqueUpToIso_hom]
  exact continuousRestriction_inflation f hf φ (OrderDual.ofDual N)

end LocalClassFieldTheory
