/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentAtlasCoverage
public import FLT.Mazur.WeierstrassDividedInitialZeroInfinity

/-!
# The whole original initial slope chart belongs to the identity chart

The actual original slope-to-infinity transition proves geometric coverage
at every depth, including the stage-zero case.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hd : 0 < depth)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "p" => resolvedSplitStructure A D
local notation "inc" => Scheme.Opens.ι (Scheme.Hom.smoothLocus (resolvedSplitStructure A D))
local notation "initial" => globalTensorAtlasMap hπ data F (depth / 2) (le_refl _)
  (Fin.succ (Fin.mk (depth / 2 + 1) (by omega)))

include hd in
/-- Every point of the original initial atlas member lies in the full identity chart. -/
theorem resolvedInitialChart_range_subset_identity :
    Set.range initial ⊆ Set.range (resolvedIdentityChart A D) := by
  rw [resolvedIdentityChart_range_infinity]
  have he := initialZeroSlopeAtlasIso_map hπ data D hd rfl (depth / 2) (le_refl _)
  have hr := congrArg (fun f : _ ⟶ _ => Set.range f) he
  rw [SchemeOpenChartRange.range_iso_comp] at hr
  rw [hr]
  exact initialZeroSlopeChart_range_subset_infinity hπ data D hd rfl (depth / 2) (le_refl _)

include hd in
/-- The initial slope member is covered by the actual identity component of the smooth family. -/
theorem resolvedComponentCharts_cover_initial (r : (ResidueField A)ˣ)
    (z : (p).smoothLocus.toScheme) (hz : inc z ∈ Set.range initial) :
    z ∈ Set.range (resolvedComponentChart A D r .identity) := by
  rw [resolvedComponentChart_mem_range_iff]
  change inc z ∈ Set.range (resolvedIdentitySmoothChart A D ≫ inc)
  rw [resolvedIdentitySmoothChart_inclusion]
  exact resolvedInitialChart_range_subset_identity A D hd hz

end FLT.Mazur.WeierstrassDividedDepth
