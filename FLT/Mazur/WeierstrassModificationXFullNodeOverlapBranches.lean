/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOverlapCover
public import FLT.Mazur.WeierstrassModificationXZeroNodeOverlapBranches
public import FLT.Mazur.WeierstrassModificationXFullNodeConicBranch
public import FLT.Mazur.WeierstrassModificationXConicBoundaryCharts

/-!
# Original branch restrictions on both pieces of the full node overlap

Both actual pullback projections keep the exterior slope translation and
their full conic parameters. The conic piece requires an invertible constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "f" => fullFirstNodeChart a c ha
local notation "g" => fullSecondNodeChart a c ha
local notation "e" => fullNodeOverlapExterior a c ha

/-- The exterior's first projection is the original localized incidence branch. -/
@[reassoc] theorem fullNodeOverlapExterior_first :
    e ≫ pullback.fst f g =
      fullNodeSlopeFirstBranch a c ha ≫ fullNodeSecondBranch a c ha := by
  apply (cancel_mono f).mp
  rw [Category.assoc, fullNodeOverlapExterior_global,
    Category.assoc, fullNodeSecondBranch_firstChart,
    fullNodeSlopeFirstBranch_open_assoc, fiberExteriorSlopeChart_incidence]

/-- The opposite exterior projection retains its exact slope translation. -/
@[reassoc] theorem fullNodeOverlapExterior_second :
    e ≫ pullback.snd f g =
      fullNodeSlopeSecondBranch a c ha ≫ fullNodeSecondBranch (-a) c ha.neg := by
  apply (cancel_mono g).mp
  rw [Category.assoc, ← pullback.condition, fullNodeOverlapExterior_global,
    Category.assoc, fullNodeSecondBranch_secondChart,
    fullNodeSlopeSecondBranch_open_assoc, fiberExteriorSlopeChart_incidence]

variable (hc : IsUnit c)
local notation "i" => Iso.hom (fiberConicOpenIso a c) ≫ fullNodeOverlapConic a c ha hc

/-- The conic incidence piece retains the full first node parameter restriction. -/
@[reassoc] theorem fullNodeOverlapConic_first :
    i ≫ pullback.fst f g = conicIncidenceFirstParameterMap a c ha hc ≫
      (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha := by
  apply (cancel_mono f).mp
  simp only [Category.assoc]
  rw [fullNodeOverlapConic_global, fiberConicOpenIso_inclusion,
    fullNodeFirstBranch_firstChart, conicIncidenceFirstParameterMap_conic_assoc]
  rfl

/-- The conic incidence piece retains the entire opposite original parameter restriction. -/
@[reassoc] theorem fullNodeOverlapConic_second :
    i ≫ pullback.snd f g = conicIncidenceSecondParameterMap a c ha hc ≫
      (fullNodeConicParameterIso (-a) c ha.neg).hom ≫ fullNodeFirstBranch (-a) c ha.neg := by
  apply (cancel_mono g).mp
  simp only [Category.assoc]
  rw [← pullback.condition, fullNodeOverlapConic_global, fiberConicOpenIso_inclusion,
    fullNodeFirstBranch_secondChart, conicIncidenceSecondParameterMap_conic_assoc]
  rfl

end FLT.Mazur.WeierstrassModificationX
