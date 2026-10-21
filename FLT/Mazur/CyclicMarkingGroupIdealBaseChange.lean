/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSmoothCarrier
public import FLT.Mazur.ClosedGroupIdealCarrierBaseChange
public import FLT.Mazur.RelativeCartierOriginalSquare

/-!
# The full smooth-group orbit ideal under arbitrary base change

No multiplication equation is assumed. The actual ideal, its Cartier module,
and its full closed carrier all commute with parameter change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group)) (g : T ⟶ S)

/-- The group orbit ideal itself commutes with nonflat parameter change. -/
theorem cyclicMarkingGroupIdeal_baseChange :
    (E.baseChange g).cyclicMarkingGroupIdeal (pullCyclicMarking (E := E) g φ) =
      (E.cyclicMarkingGroupIdeal φ).comap (pullback.fst E.group.hom g) := by
  rw [cyclicMarkingGroupIdeal_eq_comap, cyclicMarkingGroupIdeal_eq_comap,
    cyclicMarkingIdeal_baseChange, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp]
  congr 1
  rw [baseChange_inclusion]
  exact (OverPullbackLocalPushout.map_isPullback g E.inclusion).w

/-- The full group carrier is cartesian before imposing subgroup closure. -/
def cyclicMarkingGroupBaseChangeIso :
    ClosedGroupIdeal.carrier (E.baseChange g).group
        ((E.baseChange g).cyclicMarkingGroupIdeal (pullCyclicMarking (E := E) g φ)) ≅
      (Over.pullback g).obj (ClosedGroupIdeal.carrier E.group (E.cyclicMarkingGroupIdeal φ)) :=
  ClosedGroupIdeal.carrierBaseChangeIso E.group (E.cyclicMarkingGroupIdeal φ) g _
    (E.cyclicMarkingGroupIdeal_baseChange φ g).symm

variable [SmoothOfRelativeDimension 1 E.group.hom]

/-- The original group orbit ideal is a relative Cartier divisor. -/
theorem cyclicMarkingGroupIdeal_cartier :
    FCurve.RelativeEffectiveCartier E.group.hom (E.cyclicMarkingGroupIdeal φ) := by
  rw [cyclicMarkingGroupIdeal_eq_comap, ← E.inclusion.w]
  exact (E.cyclicMarkingIdeal_smoothOpen_cartier φ).comap_of_isOpenImmersion E.inclusion.left

/-- Its canonical module comparison is invertible even for a nonflat parameter map. -/
theorem cyclicMarkingGroupIdeal_pullback_isIso :
    IsIso (FCurve.idealModulePullbackHom (E.cyclicMarkingGroupIdeal φ)
      (pullback.fst E.group.hom g)) :=
  FCurve.relativeCartierIdealPullback_originalSquare (IsPullback.of_hasPullback E.group.hom g)
    (E.cyclicMarkingGroupIdeal φ) (E.cyclicMarkingGroupIdeal_cartier φ)

end FLT.Mazur.GeneralizedEllipticCurve
