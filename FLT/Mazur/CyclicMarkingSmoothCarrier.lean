/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSmoothRestriction
public import FLT.Mazur.ClosedGroupIdealGroup

/-!
# The smooth-group carrier of a cyclic orbit divisor

The closed image of the lifted divisor is its exact multiplicity-preserving
restriction. Its canonical isomorphism to the whole-curve divisor transfers
the degree without a smoothness assumption on the entire curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- The actual closed orbit ideal inside the given smooth group. -/
def cyclicMarkingGroupIdeal : E.group.left.IdealSheafData :=
  (E.cyclicMarkingSmoothLift φ).ker

/-- The group ideal is the restriction of the whole orbit divisor, with all multiplicities. -/
theorem cyclicMarkingGroupIdeal_eq_comap :
    E.cyclicMarkingGroupIdeal φ = (E.cyclicMarkingIdeal φ).comap E.inclusion.left :=
  E.cyclicMarkingSmoothLift_ker φ

/-- Every cyclic label contributes its original group-section ideal. -/
theorem cyclicMarkingGroupIdeal_eq_prod :
    E.cyclicMarkingGroupIdeal φ = ∏ i : Fin n, (φ (.ofAdd (i.val : ZMod n))).left.ker := by
  rw [cyclicMarkingGroupIdeal_eq_comap, cyclicMarkingIdeal_restrict_smooth]

/-- The whole orbit divisor and its smooth-group carrier are canonically the same base scheme. -/
def cyclicMarkingGroupCarrierIso :
    Over.mk ((E.cyclicMarkingIdeal φ).subschemeι ≫ E.curve.hom) ≅
      ClosedGroupIdeal.carrier E.group (E.cyclicMarkingGroupIdeal φ) :=
  Over.isoMk (asIso (E.cyclicMarkingSmoothLift φ).toImage) (by
    change (E.cyclicMarkingSmoothLift φ).toImage ≫
      (E.cyclicMarkingSmoothLift φ).imageι ≫ E.group.hom = _
    rw [Scheme.Hom.toImage_imageι_assoc, ← E.inclusion.w,
      cyclicMarkingSmoothLift_inclusion_assoc]
    rfl)

/-- The comparison retains the original smooth-group immersion. -/
@[reassoc] theorem cyclicMarkingGroupCarrierIso_inclusion :
    (E.cyclicMarkingGroupCarrierIso φ).hom.left ≫
      (E.cyclicMarkingGroupIdeal φ).subschemeι = E.cyclicMarkingSmoothLift φ :=
  (E.cyclicMarkingSmoothLift φ).toImage_imageι

/-- The inverse carrier comparison retains the actual whole-curve divisor immersion. -/
@[reassoc] theorem cyclicMarkingGroupCarrierIso_inv_curve :
    (E.cyclicMarkingGroupCarrierIso φ).inv.left ≫ (E.cyclicMarkingIdeal φ).subschemeι =
      (E.cyclicMarkingGroupIdeal φ).subschemeι ≫ E.inclusion.left := by
  apply (cancel_epi (E.cyclicMarkingGroupCarrierIso φ).hom.left).mp
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id]
  change (𝟙 _) ≫ _ = _
  rw [Category.id_comp, cyclicMarkingGroupCarrierIso_inclusion_assoc,
    cyclicMarkingSmoothLift_inclusion]

/-- The group carrier has degree n even at singular fibers and repeated labels. -/
theorem cyclicMarkingGroupIdeal_degree [SmoothOfRelativeDimension 1 E.group.hom] :
    FCurve.FiniteLocallyFreeDegree
      ((E.cyclicMarkingGroupIdeal φ).subschemeι ≫ E.group.hom) n :=
  (E.cyclicMarkingIdeal_smoothOpen_degree φ).of_overIso (E.cyclicMarkingGroupCarrierIso φ)

end FLT.Mazur.GeneralizedEllipticCurve
