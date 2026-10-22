/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementSectionRatios
public import FLT.Mazur.DivisorLineTensorSectionCompatibility
public import FLT.Mazur.ModuleSectionRatioOpenNaturality
public import FLT.Mazur.ModuleSectionRatioOpenIso
public import FLT.Mazur.ModuleSectionProjectiveChartNaturality

/-!
# Actual complement functions under a section-preserving line comparison

The canonical denominator is preserved in every positive degree. Its
section ratio therefore pulls back along the actual restricted scheme map,
without reducedness, flatness, or a choice of affine coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback
variable {X Y : Scheme} (f : X ⟶ Y) {I : Y.IdealSheafData} {J : X.IdealSheafData}
  (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
  (e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ)
  (he : DivisorLineSectionCompatible f hI hJ e)
  (hU : J.support.compl ≤ f ⁻¹ᵁ I.support.compl)

include he

/-- The restricted original morphism pulls back the actual canonical-denominator function. -/
theorem divisorComplementFunction_pullback (n : ℕ) (hn : 0 < n)
    (z : Γ(tensorPower (divisorLineBundle I hI) n, ⊤)) :
    (f.resLE I.support.compl J.support.compl hU).appTop
        (divisorComplementFunction hI n z) =
      divisorComplementFunction hJ n
        ((tensorPowerPullbackComparison f e n).hom.app ⊤ (pullGlobal f _ z)) := by
  let L := tensorPower (divisorLineBundle I hI) n
  let d := tensorPowerSection (divisorLineBundle I hI) ⊤ (divisorSection hI ⊤) n
  let c := tensorPowerSection (divisorLineBundle J hJ) ⊤ (divisorSection hJ ⊤) n
  let a := tensorPowerPullbackComparison f e n
  have hd : a.hom.app ⊤ (pullGlobal f L d) = c := he.tensorPower_section n
  have hV : J.support.compl ≤ sectionGeneratorOpen ((pullback f).obj L)
      (pullGlobal f L d) := by
    rw [← sectionGeneratorOpen_iso a, hd]
    exact divisorComplement_le_powerGenerator hJ n hn
  rw [divisorComplementFunction_eq_ratio hI n hn,
    divisorComplementFunction_eq_ratio hJ n hn, resLE_topIso_inv,
    sectionRatioOn_pullback f L I.support.compl J.support.compl hU d z
      (divisorComplement_le_powerGenerator hI n hn) hV]
  congr 1
  have hi := sectionRatioOn_iso a (pullGlobal f L d) (pullGlobal f L z) J.support.compl hV
  simpa only [hd] using hi.symm

end FLT.Mazur.FCurve
