/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicInput
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicLift

/-!
# Literal complete-graph restrictions above every original adic node chart

Restrict the actual base-changed complete graph to the full original node
inputs. These proper surjective correspondences carry maps to the original
adic polygon and retain the cubic contraction equation. They are flat over
the original truncated coefficient base; no finite-image identification or
flatness over the larger Laurent coefficient ring is inferred here.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (j : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "c" => PolygonInfinitesimal.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h j

/-- The complete graph restricted to an entire original variable-parameter adic node chart. -/
abbrev completeIdentityActionGraphAdicNode : Scheme := pullback (p) (c)

/-- Its actual projection includes every point of the original full node input. -/
abbrev completeIdentityActionGraphAdicNodeProjection := pullback.snd (p) (c)

/-- The restriction map retains the complete graph, rather than its schematic image. -/
abbrev completeIdentityActionGraphAdicNodeInclusion := pullback.fst (p) (c)

instance completeIdentityActionGraphAdicNodeProjection_proper :
    IsProper (completeIdentityActionGraphAdicNodeProjection K n h m j) := inferInstance

instance completeIdentityActionGraphAdicNodeProjection_surjective :
    Surjective (completeIdentityActionGraphAdicNodeProjection K n h m j) := inferInstance

instance completeIdentityActionGraphAdicNodeInclusion_open :
    IsOpenImmersion (completeIdentityActionGraphAdicNodeInclusion K n h m j) := inferInstance

/-- The literal node restriction's original truncated-base structure. -/
def completeIdentityActionGraphAdicNodeStructure :
    completeIdentityActionGraphAdicNode K n h m j ⟶ Spec (.of (A)) :=
  completeIdentityActionGraphAdicNodeInclusion K n h m j ≫
    completeIdentityActionGraphStageStructure K n h m

/-- The full original node correspondence inherits flatness over the original truncated base. -/
instance completeIdentityActionGraphAdicNodeStructure_flat :
    Flat (completeIdentityActionGraphAdicNodeStructure K n h m j) := by
  unfold completeIdentityActionGraphAdicNodeStructure
  infer_instance

/-- The node correspondence carries a genuine morphism into the unchanged original stage. -/
def completeIdentityActionGraphAdicNodeLift :
    completeIdentityActionGraphAdicNode K n h m j ⟶ (family K m n h).left :=
  completeIdentityActionGraphAdicNodeInclusion K n h m j ≫
    completeIdentityActionGraphStageOriginalLift K n h m

/-- This is a lift of the original cubic action on all original node inputs. -/
@[reassoc] theorem completeIdentityActionGraphAdicNodeLift_contraction :
    completeIdentityActionGraphAdicNodeLift K n h m j ≫
        originalStageToCompatibleProj K n h m ≫ completePointToIntegralCubic K n h 0 =
      completeIdentityActionGraphAdicNodeProjection K n h m j ≫ (c) ≫
        completeIdentityFiniteInput K n h 0 m ≫ completeIdentityActionTarget K n h 0 := by
  rw [completeIdentityActionGraphAdicNodeLift, Category.assoc,
    completeIdentityActionGraphStageOriginalLift_contraction,
    ← completeIdentityActionGraphStageOriginalProjection_input_assoc,
    pullback.condition_assoc]

/-- The original-stage target retains exactly the node correspondence's coefficient map. -/
@[reassoc] theorem completeIdentityActionGraphAdicNodeLift_structure :
    completeIdentityActionGraphAdicNodeLift K n h m j ≫ (family K m n h).hom =
      completeIdentityActionGraphAdicNodeStructure K n h m j := by
  rw [completeIdentityActionGraphAdicNodeLift, Category.assoc,
    completeIdentityActionGraphStageOriginalLift_structure]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
