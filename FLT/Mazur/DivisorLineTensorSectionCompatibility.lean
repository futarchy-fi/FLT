/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionCompatibility
public import FLT.Mazur.TensorPowerPullbackComparison
public import FLT.Mazur.ModuleSectionMap

/-!
# Canonical sections of tensor powers under line comparisons

An actual section-preserving comparison preserves every pure tensor power of
the canonical section. Degree zero uses the original structure-module unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor tensorIso
variable {X Y : Scheme}

/-- The actual tensor-power congruence preserves pure tensor powers on every open. -/
theorem tensorPowerCongr_section {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(M, U)) (d : ℕ) :
    (tensorPowerCongr e d).hom.app U (tensorPowerSection M U s d) =
      tensorPowerSection N U (e.hom.app U s) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (ModuleSheafTensor.map e.hom (tensorPowerCongr e d).hom).app U
      (ModuleSheafTensor.pure _ _ U s (tensorPowerSection M U s d)) = _
    rw [ModuleSheafTensor.map_pure, ih]
    rfl

variable {I : Y.IdealSheafData} {J : X.IdealSheafData}

/-- Equality of the actual powered canonical sections after pullback and comparison. -/
def DivisorLinePowerSectionCompatible (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J)
    (e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ) (d : ℕ) : Prop :=
  (tensorPowerPullbackComparison f e d).hom.app ⊤
      (pullGlobal f _ (tensorPowerSection _ ⊤ (divisorSection hI ⊤) d)) =
    tensorPowerSection _ ⊤ (divisorSection hJ ⊤) d

/-- Section preservation in degree one supplies preservation in every tensor degree. -/
theorem DivisorLineSectionCompatible.tensorPower_section {f : X ⟶ Y}
    {hI : EffectiveCartier I} {hJ : EffectiveCartier J}
    {e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}
    (he : DivisorLineSectionCompatible f hI hJ e) (d : ℕ) :
    DivisorLinePowerSectionCompatible f hI hJ e d := by
  change (tensorPowerCongr e d).hom.app ⊤
    ((tensorPowerIso f _ d).hom.app ⊤
      (pullGlobal f _ (tensorPowerSection _ ⊤ (divisorSection hI ⊤) d))) = _
  rw [tensorPowerSection_pullback, tensorPowerCongr_section]
  have hs := pullGlobal_section_map f (divisorSectionMap hI) (divisorSectionMap hJ)
    e.hom he.section
  have hs' : e.hom.app ⊤ (pullGlobal f _ (divisorSection hI ⊤)) =
      divisorSection hJ ⊤ := hs
  rw [hs']

end FLT.Mazur.FCurve
