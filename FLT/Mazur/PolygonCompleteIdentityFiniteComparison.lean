/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalEdgeExt
public import FLT.Mazur.PolygonCompleteIdentityFiniteCoherence

/-!
# Detecting the original finite cubic comparison on full Laurent edges

The original cubic comparison, including every nonreduced node, is
equivalent to its restrictions to all full Laurent edges. This is a
detection theorem; the remaining edge equations are not assumed to hold.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "c" => completePointToIntegralCubic K n h 0
local notation "a" => completeIdentityActionTarget K n h 0
local notation "f" => completeIdentityFiniteScaling K n h m
local notation "q" => completeIdentityFiniteInput K n h 0 m
local notation "s" => integralCurveStructure (completePointWeierstrassCurve K n h 0)

/-- The two actual candidates have the same original cubic coefficient morphism. -/
theorem completeIdentityFiniteComparison_base : (f) ≫ (c) ≫ (s) = (q) ≫ (a) ≫ (s) := by
  rw [completePointToIntegralCubic_over, completeIdentityActionTarget_structure,
    completeIdentityFiniteScaling_base_assoc K n h 0 m]

/-- Full Laurent edge comparisons suffice even at every original infinitesimal node. -/
theorem completeIdentityFiniteComparison_iff_edges :
    (f) ≫ (c) = (q) ≫ (a) ↔
      ∀ i : Fin n, edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i ≫ (f) ≫ (c) =
        edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i ≫ (q) ≫ (a) := by
  constructor
  · intro he i
    exact congrArg (edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i ≫ ·) he
  · intro he
    apply edge_hom_ext (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (s)
    · simpa only [Category.assoc] using completeIdentityFiniteComparison_base K n h m
    · intro i
      simpa only [Category.assoc] using he i

/-- The comparison already holds on the actual unit-parameter section of the whole input. -/
@[reassoc] theorem completeIdentityFiniteComparison_one :
    scalingParameterSection (A) (t) n h 1 ≫ (f) ≫ (c) =
      scalingParameterSection (A) (t) n h 1 ≫ (q) ≫ (a) := by
  rw [completeIdentityFiniteScaling_one_assoc, completeIdentityFiniteInput_one_assoc,
    completeIdentityActionZeroGraph_target]

end FLT.Mazur.PolygonInfinitesimalStages
