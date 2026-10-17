/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicAllNodeSourceIso

/-!
# The whole original finite section is open in the literal adic graph

The original node cover and the source inverses make the section an open
immersion at every positive order. It is also the previously constructed
closed immersion. Surjectivity onto the entire graph is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "t" => parameter K (m + 1)
local notation "f" => completeIdentityAdicGraphSection K n h (m + 1)
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h (m + 1)

/-- Every original finite node maps openly into the literal graph via its actual section. -/
theorem completeIdentityAdicGraphSection_node_open (i : Fin n) :
    IsOpenImmersion (chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i ≫ (f)) := by
  rw [← completeIdentityAdicNodeSection_inclusion]
  let _ := completeIdentityAdicNodeSection_isIso K n h m i
  infer_instance

/-- The whole finite section is an open immersion on the full original source polygon. -/
theorem completeIdentityAdicGraphSection_open : IsOpenImmersion (f) := by
  apply IsOpenImmersion.of_openCover_source (f)
    (chartCover (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h)
  · intro x y hxy
    have he := congrArg (fun z ↦ (p) z) hxy
    change ((f) ≫ (p)) x = ((f) ≫ (p)) y at he
    rw [completeIdentityAdicGraphSection_projection] at he
    exact he
  · intro i
    exact completeIdentityAdicGraphSection_node_open K n h m i

/-- The original source identifies with an actual open of the unchanged adic graph. -/
def completeIdentityAdicSectionOpen :
    (completeIdentityActionGraphStage K n h (m + 1)).Opens := by
  let _ := completeIdentityAdicGraphSection_open K n h m
  exact (f).opensRange

/-- This open retains precisely the image of the actual whole-input section. -/
theorem completeIdentityAdicSectionOpen_carrier :
    (completeIdentityAdicSectionOpen K n h m :
      Set (completeIdentityActionGraphStage K n h (m + 1))) = Set.range (f) := rfl

/-- The section image is also closed, so any as-yet-uncontrolled graph part is disjoint. -/
theorem completeIdentityAdicSectionOpen_isClosed :
    IsClosed (completeIdentityAdicSectionOpen K n h m :
      Set (completeIdentityActionGraphStage K n h (m + 1))) := by
  rw [completeIdentityAdicSectionOpen_carrier]
  exact (f).isClosedMap.isClosed_range

end FLT.Mazur.PolygonInfinitesimalStages
