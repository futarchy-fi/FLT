/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedRelabelCurve
public import FLT.Mazur.CyclicBoundaryLocusTestSubgroup
public import FLT.Mazur.CompatibleSubgroupAmple

/-!
# The full universal subgroup is preserved by unrestricted relabeling

The actual orbit ideal, with repeated factors, determines a compatible
comparison over the constructed entire-curve isomorphism. Ampleness is invariant.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "C" => unrestrictedLocusCurve E n
local notation "H" => unrestrictedLocusSubgroup E n

/-- The full universal cyclic marking on the actual closed locus. -/
def unrestrictedLocusMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over (unrestrictedMultiplicationLocus E n)) ⟶ (C).group) :=
  pullCyclicMarking (unrestrictedMultiplicationLocusInclusion E n)
    (unrestrictedUniversalMarking E n)

/-- The cyclic marking is exactly the cyclic factor of the original full labels. -/
theorem unrestrictedLocusMarking_apply (j : Multiplicative (ZMod n)) :
    unrestrictedLocusMarking E n j = unrestrictedLocusLabel E n (1, 1, j) := by
  change GroupSectionBaseChange.pullSection _ (unrestrictedUniversalMarking E n j) = _
  rw [show unrestrictedUniversalMarking E n j =
    markedSection E.group n (parameter E.group n).hom (𝟙 _) (1, 1, j) from
      cyclicSectionMarking_apply E.group n _ _ j]
  rfl

/-- The universal subgroup is the full orbit ideal of that original marking. -/
theorem unrestrictedLocusSubgroup_ideal :
    (H).ideal = (C).cyclicMarkingIdeal (unrestrictedLocusMarking E n) :=
  (unrestrictedUniversalCurve E n).singularOrbitLocusSubgroup_ideal _

/-- The constructed entire-curve map carries precisely the permuted cyclic labels. -/
theorem unrestrictedRelabelCurveIso_cyclic (e : RelabelGroup n)
    (j : Multiplicative (ZMod n)) :
    unrestrictedLocusMarking E n (e.2.2.symm j) ≫
        (unrestrictedRelabelCurveIso E n e).hom.group =
      unrestrictedLocusTestMarking E n (unrestrictedRelabel E n e) j := by
  change _ = GroupSectionBaseChange.pullSection _ (unrestrictedLocusMarking E n j)
  rw [unrestrictedLocusMarking_apply, unrestrictedLocusMarking_apply]
  have hh := unrestrictedRelabelCurveIso_label E n e (1, 1, j)
  change unrestrictedLocusLabel E n (e.1.symm 1, e.2.1.symm 1, e.2.2.symm j) ≫ _ = _ at hh
  simpa only [map_one] using hh

/-- The original subgroup is preserved with its full curve and inclusion, without faithfulness. -/
def unrestrictedRelabelSubgroupIso (e : RelabelGroup n) :
    FiniteSubgroup.CompatibleIso (H) ((H).baseChange (unrestrictedRelabel E n e)) :=
  singularOrbitCompatibleIso (E := C)
    (F := (C).baseChange (unrestrictedRelabel E n e))
    ((unrestrictedLocusMarking E n).comp e.2.2.symm.toMonoidHom)
    (unrestrictedLocusTestMarking E n (unrestrictedRelabel E n e))
    (unrestrictedRelabelCurveIso E n e) (unrestrictedRelabelCurveIso_cyclic E n e)
    (H) _ (by rw [cyclicMarkingIdeal_relabel, unrestrictedLocusSubgroup_ideal])
    (unrestrictedLocusTestSubgroup_ideal E n _)

/-- The subgroup comparison retains the specified entire-curve isomorphism. -/
theorem unrestrictedRelabelSubgroupIso_curve (e : RelabelGroup n) :
    (unrestrictedRelabelSubgroupIso E n e).curve = unrestrictedRelabelCurveIso E n e :=
  singularOrbitCompatibleIso_curve _ _ _ _ _ _ _ _

/-- The full subgroup's ampleness is preserved and reflected by the unrestricted action. -/
theorem unrestrictedRelabelSubgroup_isAmple_iff (e : RelabelGroup n) :
    (H).IsAmple ↔ ((H).baseChange (unrestrictedRelabel E n e)).IsAmple :=
  (unrestrictedRelabelSubgroupIso E n e).isAmple_iff

end FLT.Mazur.CyclicBoundaryParameter
