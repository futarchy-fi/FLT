/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCanonicalMap
public import FLT.Mazur.PolygonArithmeticStageProper
public import FLT.Mazur.ProperAmpleRetainedProjIso
public import FLT.Mazur.SectionRetainedProjStructuralMap

/-!
# Recovering the original proper polygon stages

Each retained section Proj is isomorphic to the original polygon stage via
its actual section-evaluation map. The isomorphism retains the original
arithmetic base and transfers the proved flatness and properness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family
  SectionRetainedProjConstruction.toProj SectionRetainedProjStructuralMap.toBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Actual section evaluation is an isomorphism from each original polygon stage. -/
theorem boundaryStageToExactVeroneseProj_isIso (m : ℕ) :
    IsIso (boundaryStageToExactVeroneseProj A π hne hgen n h m) := by
  let _ := family_proper A π hgen m n h
  exact ProperAmpleRetainedProjIso.isIso (family A π m n h).hom (boundaryLine A π m n h)
    (exactVeroneseStep A π hne hgen n h) (boundaryLine_ample A π hgen m n h)
    (exactVeroneseStep_pos A π hne hgen n h) (boundaryExactRetainedGenerated A π hne hgen n h m)

/-- The recovery isomorphism uses the original scheme and the original evaluation morphism. -/
def boundaryStageRetainedIso (m : ℕ) :
    (family A π m n h).left ≅ boundaryExactVeroneseProj A π n h hne hgen m := by
  let _ := boundaryStageToExactVeroneseProj_isIso A π hne hgen n h m
  exact asIso (boundaryStageToExactVeroneseProj A π hne hgen n h m)

/-- Stage recovery retains its independently constructed canonical evaluation map. -/
theorem boundaryStageRetainedIso_hom (m : ℕ) :
    (boundaryStageRetainedIso A π hne hgen n h m).hom = boundaryStageToExactVeroneseProj A π
      hne hgen n h m := rfl

/-- The retained Proj's structural map to the original arithmetic base. -/
def boundaryRetainedProjToOriginalBase (m : ℕ) :
    boundaryExactVeroneseProj A π n h hne hgen m ⟶ Spec (.of (Quotient A π m)) :=
  SectionRetainedProjStructuralMap.toBase (boundaryLine A π m n h)
    (exactVeroneseStep A π hne hgen n h) (family A π m n h).hom

/-- Recovery retains the actual original stage structure morphism. -/
@[reassoc]
theorem boundaryStageRetainedIso_toOriginalBase (m : ℕ) :
    (boundaryStageRetainedIso A π hne hgen n h m).hom ≫ boundaryRetainedProjToOriginalBase A π
      hne hgen n h m =
      (family A π m n h).hom :=
  SectionRetainedProjStructuralMap.toProj_toBase (boundaryLine A π m n h)
    (exactVeroneseStep A π hne hgen n h) (family A π m n h).hom (boundaryExactRetainedGenerated
      A π hne hgen n h m)

/-- The inverse recovery map also preserves the original base morphism. -/
@[reassoc]
theorem boundaryStageRetainedIso_inv_toOriginalBase (m : ℕ) :
    (boundaryStageRetainedIso A π hne hgen n h m).inv ≫ (family A π m n h).hom =
      boundaryRetainedProjToOriginalBase A π hne hgen n h m := by
  rw [← boundaryStageRetainedIso_toOriginalBase A π hne hgen n h m, Iso.inv_hom_id_assoc]

/-- The recovered stage Proj retains the proved flatness of the original infinitesimal family. -/
theorem boundaryRetainedProjToOriginalBase_flat (m : ℕ) :
    Flat (boundaryRetainedProjToOriginalBase A π hne hgen n h m) := by
  rw [← boundaryStageRetainedIso_inv_toOriginalBase A π hne hgen n h m]
  infer_instance

/-- The recovered stage Proj retains the proved properness of the original infinitesimal family. -/
theorem boundaryRetainedProjToOriginalBase_proper (m : ℕ) :
    IsProper (boundaryRetainedProjToOriginalBase A π hne hgen n h m) := by
  rw [← boundaryStageRetainedIso_inv_toOriginalBase A π hne hgen n h m]
  let _ := family_proper A π hgen m n h
  infer_instance

end FLT.Mazur.PolygonArithmeticStages
