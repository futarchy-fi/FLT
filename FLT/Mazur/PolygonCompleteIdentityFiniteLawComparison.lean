/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFinitePair
public import FLT.Mazur.PolygonInfinitesimalUniversalEdges

/-!
# The precise original multiplication equation on the finite identity edge

Universal scaling on the identity edge is literal Laurent scaling. The
prescribed cubic action there is actual original group multiplication.
Since the identity contraction is an open immersion, their cubic comparison
is equivalent to equality in the original identity group itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "U" => completePointIdentityOpen K n h i
local notation "e" => completeIdentityStageTorus K n h i m
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i
local notation "c" => completePointToIntegralCubic K n h i

/-- Finite polygon scaling on the identity edge is the actual full Laurent multiplication map. -/
@[reassoc] theorem completeIdentityFiniteScaling_identityEdge :
    (j) ≫ completeIdentityFiniteScaling K n h m =
      universalEdgeScaling (A) ≫ (e) ≫ (U).ι := by
  rw [completeIdentityFiniteScaling, edge_universalScaling_assoc,
    completeIdentityStageTorus_inclusion]

/-- The remaining identity-edge cubic equation is exactly the original group-law equation. -/
theorem completeIdentityFiniteComparison_iff_originalMul :
    (j) ≫ completeIdentityFiniteScaling K n h m ≫ (c) =
        (j) ≫ completeIdentityFiniteInput K n h i m ≫
          completeIdentityActionTarget K n h i ↔
      universalEdgeScaling (A) ≫ (e) = completeIdentityFiniteOriginalMul K n h i m := by
  let _ : Mono ((U).ι ≫ (c)) := by
    rw [← completePointSmoothCubicIso_inclusion]
    infer_instance
  rw [completeIdentityFiniteScaling_identityEdge_assoc,
    ← completeIdentityFiniteOriginalMul_cubic]
  simpa only [Category.assoc] using
    (cancel_mono ((U).ι ≫ (c)) (g := universalEdgeScaling (A) ≫ (e))
      (h := completeIdentityFiniteOriginalMul K n h i m))

end FLT.Mazur.PolygonInfinitesimalStages
