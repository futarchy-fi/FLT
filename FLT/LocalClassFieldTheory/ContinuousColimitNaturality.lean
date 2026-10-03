/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCoefficientMaps
public import FLT.LocalClassFieldTheory.ContinuousCohomologyColimit

/-!
# Coefficient naturality of the continuous colimit

The finite-stage coefficient maps form a natural transformation. The colimit
comparison intertwines its induced map with the actual continuous coefficient map.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits HomologicalComplex

variable {k G M P : Type u} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k G M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)

/-- Coefficient maps commute with all finite-stage refinements. -/
def invariantStageCoefficientNat (φ : RM ⟶ RP) :
    invariantStageDiagram k G M ⟶ invariantStageDiagram k G P where
  app N := invariantStageCoefficientMap φ (OrderDual.ofDual N).toSubgroup
  naturality N P f := by ext n c; rfl

/-- The complex colimit comparison is natural in the coefficient module. -/
theorem continuousCochainsColimitIso_naturality (φ : RM ⟶ RP) :
    colimMap (invariantStageCoefficientNat φ) ≫ (continuousCochainsColimitIso k G P).hom =
      (continuousCochainsColimitIso k G M).hom ≫ continuousCoefficientMap φ := by
  apply colimit.hom_ext
  intro N
  rw [ι_colimMap_assoc]
  change (invariantStageCoefficientNat φ).app N ≫
    colimit.ι _ N ≫ ((colimit.isColimit _).coconePointUniqueUpToIso
      (continuousCochainsIsColimit k G P)).hom =
    (colimit.ι _ N ≫ ((colimit.isColimit _).coconePointUniqueUpToIso
      (continuousCochainsIsColimit k G M)).hom) ≫ continuousCoefficientMap φ
  rw [colimit.comp_coconePointUniqueUpToIso_hom,
    colimit.comp_coconePointUniqueUpToIso_hom]
  exact continuousCoefficientMap_inflation φ (OrderDual.ofDual N)


/-- The induced map on the actual continuous cohomology modules. -/
def continuousCoefficientCohomologyMap (φ : RM ⟶ RP) (n : ℕ) :
    continuousCohomology k G M n ⟶ continuousCohomology k G P n :=
  homologyMap (continuousCoefficientMap φ) n

/-- Finite-stage cohomology coefficient maps form a natural transformation. -/
def invariantStageCohomologyCoefficientNat (φ : RM ⟶ RP) (n : ℕ) :
    invariantStageCohomologyDiagram k G M n ⟶ invariantStageCohomologyDiagram k G P n :=
  Functor.whiskerRight (invariantStageCoefficientNat φ)
    (homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n)

/-- Coefficient naturality also holds for the cohomology colimit comparison. -/
theorem continuousCohomologyColimitIso_naturality (φ : RM ⟶ RP) (n : ℕ) :
    colimMap (invariantStageCohomologyCoefficientNat φ n) ≫
        (continuousCohomologyColimitIso k G P n).hom =
      (continuousCohomologyColimitIso k G M n).hom ≫ continuousCoefficientCohomologyMap φ n := by
  apply colimit.hom_ext
  intro N
  rw [ι_colimMap_assoc]
  change (invariantStageCohomologyCoefficientNat φ n).app N ≫
    colimit.ι _ N ≫ ((colimit.isColimit _).coconePointUniqueUpToIso
      (continuousCohomologyIsColimit k G P n)).hom =
    (colimit.ι _ N ≫ ((colimit.isColimit _).coconePointUniqueUpToIso
      (continuousCohomologyIsColimit k G M n)).hom) ≫ continuousCoefficientCohomologyMap φ n
  rw [colimit.comp_coconePointUniqueUpToIso_hom,
    colimit.comp_coconePointUniqueUpToIso_hom]
  exact (homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun f => homologyMap f n)
      (continuousCoefficientMap_inflation φ (OrderDual.ofDual N))).trans
        (homologyMap_comp _ _ n))

end LocalClassFieldTheory
