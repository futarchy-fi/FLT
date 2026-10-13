/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionCompatibility
public import FLT.Mazur.DivisorLineBundleSumUnit

/-!
# Transport of section comparisons along equality of Cartier ideals

Relabeling a marking changes its expression but not its ideal. These formulas
retain the explicit sheaf isomorphisms needed for cocycle equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme} {I I' : Y.IdealSheafData} {J J' : X.IdealSheafData}

/-- Transport of an ideal preserves the original canonical vanishing section. -/
@[reassoc] theorem divisorLineBundleEqIso_section (w : J = J')
    (hJ : EffectiveCartier J) (hJ' : EffectiveCartier J') :
    divisorSectionMap hJ ≫ (divisorLineBundleEqIso w hJ hJ').hom =
      divisorSectionMap hJ' := by
  subst J'
  simp [divisorLineBundleEqIso]

/-- Rewriting the source ideal retains the actual section comparison. -/
theorem DivisorLineSectionCompatible.sourceIdealEq {f : X ⟶ Y}
    {hI : EffectiveCartier I} {hI' : EffectiveCartier I'} {hJ : EffectiveCartier J}
    {e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}
    (he : DivisorLineSectionCompatible f hI hJ e) (w : I' = I) :
    DivisorLineSectionCompatible f hI' hJ
      ((pullback f).mapIso (divisorLineBundleEqIso w hI' hI) ≪≫ e) := by
  subst I'
  simpa [divisorLineBundleEqIso] using he

/-- Rewriting the target ideal retains the actual section comparison. -/
theorem DivisorLineSectionCompatible.targetIdealEq {f : X ⟶ Y}
    {hI : EffectiveCartier I} {hJ : EffectiveCartier J} {hJ' : EffectiveCartier J'}
    {e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}
    (he : DivisorLineSectionCompatible f hI hJ e) (w : J = J') :
    DivisorLineSectionCompatible f hI hJ'
      (e ≪≫ divisorLineBundleEqIso w hJ hJ') := by
  subst J'
  simpa [divisorLineBundleEqIso] using he

end FLT.Mazur.FCurve
