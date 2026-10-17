/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedBoundarySupport
public import FLT.Mazur.PolygonCollapsedFiberReduced

/-!
# Full boundary ideals of the collapsed chain

Radicality of the actual fiber upgrades the computed boundary support to an
equality of ideal sheaves with the surviving complete branch kernel.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedBoundaryIdeal
open PolygonCyclicAtlas PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "F" => fiberIdeal K n (by omega) (normalization K n h)
  (nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega)) i

/-- Every full chart restriction of the actual fiber ideal is radical. -/
theorem chart_radical (j : Fin n) :
    ((F).comap (chart K n h j)).radical = (F).comap (chart K n h j) := by
  rw [← IdealSheafRadicalOpen.comap_radical,
    PolygonCollapsedFiberReduced.fiberIdeal_radical]

/-- The retained boundary has exactly the kernel of the whole second branch. -/
theorem retained_chart : (F).comap (chart K n h i) = (secondBranch K).ker := by
  rw [← chart_radical K n h i i, ← IdealSheafRadicalOpen.ker_radical (secondBranch K),
    ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker,
    (secondBranch K).isClosedEmbedding.isClosed_range.closure_eq]
  exact PolygonCollapsedBoundarySupport.retained_support K n h i

/-- The predecessor boundary has exactly the kernel of the whole first branch. -/
theorem predecessor_chart :
    (F).comap (chart K n h ((finRotate n).symm i)) = (firstBranch K).ker := by
  rw [← chart_radical K n h i ((finRotate n).symm i),
    ← IdealSheafRadicalOpen.ker_radical (firstBranch K),
    ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker,
    (firstBranch K).isClosedEmbedding.isClosed_range.closure_eq]
  exact PolygonCollapsedBoundarySupport.predecessor_support K n h i

end FLT.Mazur.PolygonCollapsedBoundaryIdeal
