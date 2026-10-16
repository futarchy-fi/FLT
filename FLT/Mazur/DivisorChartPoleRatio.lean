/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorChartTensorNumerator
public import FLT.Mazur.DivisorComplementSectionRatios

/-!
# A degree-bounded equation for the actual canonical pole ratio

Restrict the original tensor numerator identity to any subopen where the
canonical power generates. The same numerator clears the actual function's
denominator with exactly the original pole degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
universe u
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)
variable (U : X.affineOpens) (a : Γ(X, U)) (ha : IsRegular a)
variable (he : I.ideal U = Ideal.span {a}) (d : ℕ)
local notation "L" => divisorLineBundle I hI
local notation "M" => tensorPower (L) d
local notation "c" => tensorPowerSection (L) ⊤ (divisorSection hI ⊤) d

/-- The original numerator clears the actual canonical section ratio in its own degree. -/
theorem divisorChartTensorNumerator_ratio (V : X.Opens) (hVU : V ≤ U.1)
    (hV : V ≤ sectionGeneratorOpen (M) (c)) (s : Γ((M), ⊤)) :
    (X.presheaf.map (homOfLE hVU).op a) ^ d * sectionRatioOn (M) (c) V hV s =
      X.presheaf.map (homOfLE hVU).op
        (divisorChartTensorNumerator hI U a ha he d
          ((M).presheaf.map U.1.leTop.op s)) := by
  let _ := sectionGeneratorOpen_app_isIso (M) (c) V hV
  apply (ConcreteCategory.bijective_of_isIso ((globalSectionHom (M) (c)).app V)).injective
  change ((X.presheaf.map (homOfLE hVU).op a) ^ d *
    sectionRatioOn (M) (c) V hV s) • (M).presheaf.map V.leTop.op (c) =
      (X.presheaf.map (homOfLE hVU).op
        (divisorChartTensorNumerator hI U a ha he d
          ((M).presheaf.map U.1.leTop.op s))) • (M).presheaf.map V.leTop.op (c)
  rw [mul_smul]
  have hr := sectionRatioOn_smul (M) (c) V hV s
  change sectionRatioOn (M) (c) V hV s • (M).presheaf.map V.leTop.op (c) =
    (M).presheaf.map V.leTop.op s at hr
  rw [hr]
  have hn := congrArg ((M).presheaf.map (homOfLE hVU).op)
    (divisorChartTensorNumerator_smul hI U a ha he d
      ((M).presheaf.map U.1.leTop.op s))
  have hc : (M).presheaf.map V.leTop.op (c) =
      tensorPowerSection (L) V (divisorSection hI V) d := by
    exact (tensorPowerSection_restrict (L) (show V ≤ ⊤ from le_top)
      (divisorSection hI ⊤) d).trans
        (congrArg (fun z ↦ tensorPowerSection (L) V z d)
          (divisorSection_restrict hI (show V ≤ ⊤ from le_top)))
  rw [hc]
  simp only [Scheme.Modules.map_smul, map_pow, ← Functor.map_comp_apply,
    ← op_comp, tensorPowerSection_restrict, divisorSection_restrict] at hn
  rw [show homOfLE hVU ≫ U.1.leTop = V.leTop from Subsingleton.elim _ _] at hn
  exact hn

/-- On the original divisor complement the actual pole ratio has this same bounded equation. -/
theorem divisorChartTensorNumerator_complement_ratio (hd : 0 < d)
    (V : X.Opens) (hVU : V ≤ U.1) (hVC : V ≤ I.support.compl)
    (s : Γ((M), ⊤)) :
    (X.presheaf.map (homOfLE hVU).op a) ^ d *
      sectionRatioOn (M) (c) V
        (hVC.trans (divisorComplement_le_powerGenerator hI d hd)) s =
      X.presheaf.map (homOfLE hVU).op
        (divisorChartTensorNumerator hI U a ha he d
          ((M).presheaf.map U.1.leTop.op s)) :=
  divisorChartTensorNumerator_ratio hI U a ha he d V hVU _ s

end FLT.Mazur.FCurve
