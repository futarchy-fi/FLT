/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginIdeal
public import FLT.Mazur.PolygonCompletePointOriginParameterRestriction
public import FLT.Mazur.PolygonCompletePointRatioIdeal

/-!
# Full ideal comparison on original first-order Cartier charts

The actual pulled cubic-origin ideal equals the original marking ideal on each
Cartier chart in the first-order neighborhood. The proof uses the original
parameter and structure-sheaf maps, rather than equality of supports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i

/-- The actual cubic-origin pullback restricts through the actual parameter map. -/
theorem completePointPulledOriginIdeal_subopen (A : (exactVeroneseProj K n h).Opens)
    (hA : A ≤ (V)) :
    (completePointPulledOriginIdeal K n h i).comap A.ι =
      (originNeighborhoodSection (W)).ker.comap
        ((exactVeroneseProj K n h).homOfLE hA ≫ (q)) := by
  rw [Scheme.IdealSheafData.comap_comp,
    ← completePointPulledOriginIdeal_neighborhood,
    ← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]

/-- Every original first-order Cartier chart has equality of the full original ideals. -/
theorem completePointPulledOriginIdeal_firstOrder_chart
    (A : (exactVeroneseProj K n h).affineOpens)
    (hA : A.1 ≤ completePointFirstOrderOpen K n h i) (hC : CartierChart (s).ker A) :
    (completePointPulledOriginIdeal K n h i).ideal A = (s).ker.ideal A := by
  have he := congrArg (fun J => J.ideal ⟨⊤, isAffineOpen_top A.1.toScheme⟩)
    (completePointPulledOriginIdeal_subopen K n h i A.1 (hA.trans inf_le_left))
  rw [Scheme.IdealSheafData.ideal_comap_ι_top,
    Scheme.IdealSheafData.ideal_comap_top, originIdealSheaf_section_equation,
    Ideal.map_span, Set.image_singleton, completePointToOrigin_parameter_subopen] at he
  have hr := congrArg (Ideal.map A.1.topIso.inv.hom)
    (completePointRatio_span_marking K n h i A hA hC)
  rw [Ideal.map_span, Set.image_singleton] at hr
  have hc := congrArg (Ideal.comap A.1.topIso.inv.hom) (he.trans hr)
  simpa only [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso A.1.topIso.inv)] using hc

end FLT.Mazur.PolygonInfinitesimalStages
