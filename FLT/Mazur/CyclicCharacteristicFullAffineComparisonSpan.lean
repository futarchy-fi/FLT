/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitSchemeDescent
public import FLT.Mazur.CyclicCharacteristicResidualSchemeCover

/-!
# Full comparison spans between arbitrary residual affine charts

Restrict both ends of the original assembled comparison scheme to the selected
source charts. The resulting scheme span includes cross-characteristic arrows
and retains their original scheme maps, not only their point relation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original inclusion of a selected affine parameter chart in the assembled source. -/
def fullAffineSourceInclusion (i : InvariantAffineIndex n) :
    invariantAffineChart n i ⟶ normalizedDisjointSource n :=
  invariantAffineInclusion n i ≫ normalizedDisjointInclusion n i.1

/-- Restrict the source of every original full comparison arrow to one affine chart. -/
def fullAffineComparisonFirst (i : InvariantAffineIndex n) : Scheme :=
  pullback (disjointComparisonSource n) (fullAffineSourceInclusion n i)

/-- The original target map on this source restriction. -/
def fullAffineComparisonFirstTarget (i : InvariantAffineIndex n) :
    fullAffineComparisonFirst n i ⟶ normalizedDisjointSource n :=
  pullback.fst _ _ ≫ disjointComparisonTarget n

/-- Restrict the other endpoint to any affine chart, including the opposite characteristic. -/
def fullAffineComparisonSpan (i j : InvariantAffineIndex n) : Scheme :=
  pullback (fullAffineComparisonFirstTarget n i) (fullAffineSourceInclusion n j)

/-- The original source arm of the full restricted comparison span. -/
def fullAffineComparisonSource (i j : InvariantAffineIndex n) :
    fullAffineComparisonSpan n i j ⟶ invariantAffineChart n i :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The original target arm of the full restricted comparison span. -/
def fullAffineComparisonTarget (i j : InvariantAffineIndex n) :
    fullAffineComparisonSpan n i j ⟶ invariantAffineChart n j :=
  pullback.snd _ _

/-- The two full span arms have exactly the same scheme projection to the actual quotient. -/
theorem fullAffineComparison_condition (i j : InvariantAffineIndex n) :
    fullAffineComparisonSource n i j ≫ fullAffineSourceInclusion n i ≫
        invariantOrbitSchemeProjection n =
      fullAffineComparisonTarget n i j ≫ fullAffineSourceInclusion n j ≫
        invariantOrbitSchemeProjection n := by
  dsimp only [fullAffineComparisonSource, fullAffineComparisonTarget]
  rw [Category.assoc, ← pullback.condition_assoc,
    invariantOrbitSchemeProjection_condition]
  rw [← Category.assoc, ← Category.assoc]
  change (pullback.fst _ _ ≫ fullAffineComparisonFirstTarget n i) ≫ _ = _
  rw [pullback.condition, Category.assoc]

/-- The full cross-chart residual span lies on the actual quotient overlap as scheme maps. -/
theorem fullAffineComparison_residual_condition (i j : InvariantAffineIndex n) :
    (fullAffineComparisonSource n i j ≫ affineResidualProjection n i) ≫
        affineResidualInclusion n i =
      (fullAffineComparisonTarget n i j ≫ affineResidualProjection n j) ≫
        affineResidualInclusion n j := by
  rw [Category.assoc, Category.assoc, affineResidualProjection_inclusion,
    affineResidualProjection_inclusion]
  exact fullAffineComparison_condition n i j

end FLT.Mazur.CyclicCharacteristicOrbit
