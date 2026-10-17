/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphFlatSource
public import FLT.Mazur.PolygonCompleteIdentityLiftLocus

/-!
# A flat original graph source open controls the entire graph over its image

The source-open inverse constructs an original polygon lift on its actual
input image. The existing uniqueness theorem then excludes all additional
graph structure over that image, including any other source components.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (completeIdentityActionGraphClosure K n h).Opens)
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "q" => U.ι ≫ (p)
variable [Flat (U.ι ≫ completeIdentityActionGraphProjection K n h)]
attribute [local instance] completeIdentityGraphFlatSource_open

/-- The actual image of the selected flat source open in the original complete input. -/
def completeIdentityGraphFlatSourceImage : (completeIdentityActionProduct K n h 0).Opens :=
  (q).opensRange

local notation "V" => completeIdentityGraphFlatSourceImage K n h U

/-- The source-open inverse gives an original polygon-valued lift on its entire image. -/
def completeIdentityGraphFlatSourceImageLift : (V).toScheme ⟶ exactVeroneseProj K n h :=
  (q).isoOpensRange.inv ≫ U.ι ≫ (l)

/-- This local lift has exactly the prescribed original cubic action. -/
@[reassoc] theorem completeIdentityGraphFlatSourceImageLift_contraction :
    completeIdentityGraphFlatSourceImageLift K n h U ≫ (c) = (V).ι ≫ (a) := by
  rw [completeIdentityGraphFlatSourceImageLift, Category.assoc, Category.assoc,
    completeIdentityActionGraphLift_contraction]
  change (q).isoOpensRange.inv ≫ (q) ≫ (a) = (V).ι ≫ (a)
  exact Scheme.Hom.isoOpensRange_inv_comp_assoc (q) (a)

/-- The whole original graph over this image is invertible, not only the chosen source open. -/
theorem completeIdentityGraphFlatSourceImage_projection_isIso :
    IsIso (pullback.snd (p) (V).ι) :=
  completeIdentityActionLocalLift_graph_isIso K n h (V)
    (completeIdentityGraphFlatSourceImageLift K n h U)
    (completeIdentityGraphFlatSourceImageLift_contraction K n h U)

/-- Every flat source-open image lies in the previously constructed maximal target domain. -/
theorem completeIdentityGraphFlatSourceImage_le_flatOpen :
    (V) ≤ completeIdentityActionFlatOpen K n h :=
  (completeIdentityAction_le_flatOpen_iff_exists K n h (V)).mpr
    ⟨completeIdentityGraphFlatSourceImageLift K n h U,
      completeIdentityGraphFlatSourceImageLift_contraction K n h U⟩

/-- Any original graph point admitting a flat source neighborhood has a covered input. -/
theorem completeIdentityGraphFlatSource_mem_flatOpen
    (x : completeIdentityActionGraphClosure K n h) (hx : x ∈ U) :
    (p) x ∈ completeIdentityActionFlatOpen K n h := by
  apply completeIdentityGraphFlatSourceImage_le_flatOpen K n h U
  exact ⟨⟨x, hx⟩, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
