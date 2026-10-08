/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonCoverUniversal
public import FLT.Mazur.SchemeAffineCrossRefinementRestriction

/-!
# Every cross refinement factors through the canonical common cover

The universal map of common covering rings exhibits any chosen cross refinement
as a restriction of the canonical one. Its two covering maps need not coincide.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')

/-- The canonical common cover over the base maps of a given cross refinement. -/
def canonical : C.CrossRefinement C' :=
  C.commonBaseCrossRefinement C' ρ.leftBase ρ.rightBase ρ.base_over

/-- The universal covering-ring map into the independently chosen cover. -/
def fromCanonical : ρ.canonical.coverRing ⟶ ρ.coverRing :=
  C.commonCoverLift C' ρ.leftBase ρ.rightBase ρ.ringMap ρ.leftCover ρ.rightCover
    ρ.leftSquare ρ.rightSquare

/-- The universal map leaves the common base unchanged. -/
theorem fromCanonical_square :
    ρ.canonical.ringMap ≫ ρ.fromCanonical = 𝟙 ρ.baseRing ≫ ρ.ringMap := by
  simpa only [canonical, commonBaseCrossRefinement, fromCanonical, Category.id_comp]
    using C.commonCoverMap_lift C' ρ.leftBase ρ.rightBase ρ.ringMap
      ρ.leftCover ρ.rightCover ρ.leftSquare ρ.rightSquare

/-- Restriction along the universal map recovers both original covering maps. -/
theorem canonical_restrict :
    ρ.canonical.restrict ρ.ringMap (𝟙 ρ.baseRing) ρ.fromCanonical
      ρ.fromCanonical_square ρ.faithfullyFlat = ρ := by
  cases ρ
  simp only [canonical, fromCanonical, restrict, commonBaseCrossRefinement,
    Category.comp_id, commonCoverLeft_lift, commonCoverRight_lift]

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
