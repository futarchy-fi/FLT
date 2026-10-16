/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDivisorEquationFrame
public import FLT.Mazur.DivisorLineTensorSectionCompatibility
public import FLT.Mazur.ModuleLocalScalarRelationTransport
public import FLT.Mazur.AffineImmersionSectionCoordinates

/-!
# Equation-frame coordinates on an actual affine chart

The canonical tensor section evaluates to the specified equation power.
Transporting the original clearing identity and cancelling that regular
power identifies the frame coordinate with the original image-open numerator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback AffineImmersionSectionCoordinates
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
variable {X Y : Scheme} [IsAffine X] {I : Y.IdealSheafData} {J : X.IdealSheafData}

/-- Evaluation on the equation power carries the canonical tensor section to that power. -/
theorem divisorEquationPowerFrame_canonical (hJ : EffectiveCartier J)
    (a : Γ(X, ⊤)) (ha : IsRegular a)
    (he : J.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a}) (d : ℕ) :
    (divisorEquationPowerFrame hJ a ha he d).hom.app ⊤
      (tensorPowerSection _ ⊤ (divisorSection hJ ⊤) d) = a ^ d := by
  rw [divisorEquationPowerFrame_apply, divisorChartTensorNumerator_def,
    divisorSection_power, divisorNumerator_apply, divisorSection_eval]
  change 1 * a ^ d = a ^ d
  exact one_mul _

/-- The genuine line pullback followed by equation evaluation preserves the equation power. -/
theorem divisorPulledEquationFrame_canonical (f : X ⟶ Y)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ)
    (hc : DivisorLineSectionCompatible f hI hJ e)
    (a : Γ(X, ⊤)) (ha : IsRegular a)
    (he : J.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a}) (d : ℕ) :
    (tensorPowerIso f _ d ≪≫ tensorPowerCongr e d ≪≫
      divisorEquationPowerFrame hJ a ha he d).hom.app ⊤
      (pullGlobal f _ (tensorPowerSection _ ⊤ (divisorSection hI ⊤) d)) = a ^ d := by
  have hp := hc.tensorPower_section d
  change (tensorPowerCongr e d).hom.app ⊤
    ((tensorPowerIso f _ d).hom.app ⊤
      (pullGlobal f _ (tensorPowerSection _ ⊤ (divisorSection hI ⊤) d))) = _ at hp
  simp only [sectionIso_trans]
  rw [hp, divisorEquationPowerFrame_canonical]

variable {A : Type} [CommRing A]
variable (f : Spec (.of A) ⟶ Y) [IsOpenImmersion f] (hI : EffectiveCartier I)
local notation "U" => imageAffine f
local notation "L" => divisorLineBundle I hI

/-- The original numerator determines every frame preserving the canonical equation power. -/
theorem divisorChartFrame_numerator (g : Γ(Y, (U).1)) (hg : IsRegular g)
    (he : I.ideal (U) = Ideal.span {g}) (d : ℕ)
    (e : (pullback f).obj (tensorPower (L) d) ≅ structureModule (Spec (.of A)))
    (hc : e.hom.app ⊤
      (pullGlobal f _ (tensorPowerSection _ ⊤ (divisorSection hI ⊤) d)) =
        ((f.appIso ⊤).hom g : Γ(Spec (.of A), ⊤)) ^ d)
    (s : Γ(tensorPower (L) d, ⊤)) :
    e.hom.app ⊤ (pullGlobal f _ s) = (f.appIso ⊤).hom
      (divisorChartTensorNumerator hI (U) g hg he d
        ((tensorPower (L) d).presheaf.map (U).1.leTop.op s)) := by
  have hs := divisorChartTensorNumerator_smul hI (U) g hg he d
    ((tensorPower (L) d).presheaf.map (U).1.leTop.op s)
  rw [← divisorSection_restrict hI (show (U).1 ≤ ⊤ from le_top),
    ← tensorPowerSection_restrict] at hs
  have ht := ModuleSectionTransportRestriction.pullGlobal_scalar_relation f e.hom s
    (tensorPowerSection _ ⊤ (divisorSection hI ⊤) d) (U).1
    (by intro x _; exact ⟨x, trivial, rfl⟩) (g ^ d) _ hs
  rw [hc, ← Scheme.Hom.appIso_hom'] at ht
  change ((f.appIso ⊤).hom (g ^ d) : Γ(Spec (.of A), ⊤)) *
    (show Γ(Spec (.of A), ⊤) from e.hom.app ⊤ (pullGlobal f _ s)) =
      (f.appIso ⊤).hom _ * ((f.appIso ⊤).hom g : Γ(Spec (.of A), ⊤)) ^ d at ht
  rw [map_pow, mul_comm ((f.appIso ⊤).hom _)] at ht
  have hr : IsRegular ((f.appIso ⊤).hom g : Γ(Spec (.of A), ⊤)) := by
    let q := (f.appIso ⊤).commRingCatIsoToRingEquiv
    constructor
    · intro b c hb
      change q g * b = q g * c at hb
      apply q.symm.injective
      apply hg.left
      simpa only [map_mul, RingEquiv.symm_apply_apply] using congrArg q.symm hb
    · intro b c hb
      change b * q g = c * q g at hb
      apply q.symm.injective
      apply hg.right
      simpa only [map_mul, RingEquiv.symm_apply_apply] using congrArg q.symm hb
  exact (hr.pow d).left ht

end FLT.Mazur.FCurve
