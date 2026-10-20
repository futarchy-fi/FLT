/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulOpen
public import FLT.Mazur.RelativeCyclicSubgroupSmoothOpen

/-!
# The actual universal subgroup over the faithful boundary parameter

The full original generalized curve is pulled back to the constructed open.
Smoothness is required only of its group, so singular boundary curves are included.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom]
local notation "B" => cyclicFaithfulParameter E.group n

/-- The entire original curve over the faithful parameter scheme. -/
def faithfulUniversalCurve : GeneralizedEllipticCurve (B).left := E.baseChange (B).hom

/-- The actual universal cyclic marking on the pulled-back original group. -/
def faithfulUniversalMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over (B).left) ⟶ (faithfulUniversalCurve E n).group) :=
  cyclicSectionMarking E.group n (B).hom (cyclicFaithfulInclusion E.group n)

/-- The original universal cyclic marking remains distinct on every nonempty test. -/
theorem faithfulUniversalMarking_distinct :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ faithfulUniversalMarking E n (.ofAdd i)) := by
  have hh := cyclicFaithfulSection_distinct E.group n (B).hom (𝟙 (B))
  have he : (𝟙 (B)) ≫ cyclicFaithfulInclusion E.group n =
      cyclicFaithfulInclusion E.group n := Category.id_comp _
  rw [he] at hh
  exact hh

/-- The actual finite rank-n subgroup on the full universal boundary curve. -/
def faithfulUniversalSubgroup : (faithfulUniversalCurve E n).FiniteSubgroup n :=
  (faithfulUniversalCurve E n).relativeCyclicSubgroup (faithfulUniversalMarking E n)
    (faithfulUniversalMarking_distinct E n)

/-- The universal subgroup is etale over the actual faithful open. -/
theorem faithfulUniversalSubgroup_etale : Etale (faithfulUniversalSubgroup E n).carrier.hom :=
  (faithfulUniversalCurve E n).relativeCyclicSubgroup_etale _ _

variable [SmoothOfRelativeDimension 1 E.group.hom]

/-- The actual universal divisor is Cartier across the singular boundary as well. -/
theorem faithfulUniversalSubgroup_cartier :
    FCurve.RelativeEffectiveCartier (faithfulUniversalCurve E n).curve.hom
      (faithfulUniversalSubgroup E n).ideal := by
  let _ : SmoothOfRelativeDimension 1 (faithfulUniversalCurve E n).group.hom :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom
      (B).hom inferInstance
  exact (faithfulUniversalCurve E n).relativeCyclicSubgroup_smoothOpen_cartier _ _

/-- The universal finite subgroup is cyclic on the entire original pulled-back curve. -/
theorem faithfulUniversalSubgroup_isCyclic : (faithfulUniversalSubgroup E n).IsCyclic := by
  let _ : SmoothOfRelativeDimension 1 (faithfulUniversalCurve E n).group.hom :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom
      (B).hom inferInstance
  exact (faithfulUniversalCurve E n).relativeCyclicSubgroup_smoothOpen_isCyclic _ _

end FLT.Mazur.CyclicBoundaryParameter
