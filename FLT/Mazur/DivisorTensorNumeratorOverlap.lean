/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorChartTensorNumerator
public import FLT.Mazur.DivisorSectionExact

/-!
# Compatibility of original bounded numerators on whole overlaps

Cross multiplication compares the same tensor section on two Cartier charts.
Cancellation uses the actual regular canonical section, so no reducedness
or restriction to the divisor complement is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
universe u
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)
local notation "L" => divisorLineBundle I hI

/-- The actual canonical power is faithful on every open, with its full coefficient ring. -/
theorem divisorCanonicalPower_smul_injective (d : ℕ) (W : X.Opens) :
    Function.Injective (fun r : Γ(X, W) ↦
      r • tensorPowerSection (L) W (divisorSection hI W) d) := by
  intro r s hrs
  apply divisorSectionMap_injective (hI.pow d) W
  rw [divisorSectionMap_app, divisorSectionMap_app]
  have he := congrArg ((divisorLineBundlePowerIso hI d).hom.app W) hrs
  simpa only [Hom.app_smul, divisorSection_power] using he

/-- Restricting the specified numerator identity keeps its original degree and section. -/
theorem divisorChartTensorNumerator_restrict_smul
    (U : X.affineOpens) (a : Γ(X, U)) (ha : IsRegular a)
    (he : I.ideal U = Ideal.span {a}) (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (W : X.Opens) (hW : W ≤ U.1) :
    (X.presheaf.map (homOfLE hW).op a) ^ d •
        (tensorPower (L) d).presheaf.map W.leTop.op s =
      X.presheaf.map (homOfLE hW).op
        (divisorChartTensorNumerator hI U a ha he d
          ((tensorPower (L) d).presheaf.map U.1.leTop.op s)) •
        tensorPowerSection (L) W (divisorSection hI W) d := by
  have hn := congrArg ((tensorPower (L) d).presheaf.map (homOfLE hW).op)
    (divisorChartTensorNumerator_smul hI U a ha he d
      ((tensorPower (L) d).presheaf.map U.1.leTop.op s))
  simp only [Scheme.Modules.map_smul, map_pow, ← Functor.map_comp_apply,
    ← op_comp, tensorPowerSection_restrict, divisorSection_restrict] at hn
  rw [show homOfLE hW ≫ U.1.leTop = W.leTop from Subsingleton.elim _ _] at hn
  exact hn

/-- The original numerators satisfy their exact cross-multiplied overlap equation. -/
theorem divisorChartTensorNumerator_overlap
    (U V : X.affineOpens) (a : Γ(X, U)) (b : Γ(X, V))
    (ha : IsRegular a) (hb : IsRegular b)
    (he : I.ideal U = Ideal.span {a}) (hf : I.ideal V = Ideal.span {b})
    (d : ℕ) (s : Γ(tensorPower (L) d, ⊤))
    (W : X.Opens) (hWU : W ≤ U.1) (hWV : W ≤ V.1) :
    (X.presheaf.map (homOfLE hWU).op a) ^ d *
      X.presheaf.map (homOfLE hWV).op
        (divisorChartTensorNumerator hI V b hb hf d
          ((tensorPower (L) d).presheaf.map V.1.leTop.op s)) =
    (X.presheaf.map (homOfLE hWV).op b) ^ d *
      X.presheaf.map (homOfLE hWU).op
        (divisorChartTensorNumerator hI U a ha he d
          ((tensorPower (L) d).presheaf.map U.1.leTop.op s)) := by
  apply divisorCanonicalPower_smul_injective hI d W
  dsimp only
  rw [mul_smul, mul_smul,
    ← divisorChartTensorNumerator_restrict_smul hI V b hb hf d s W hWV,
    ← divisorChartTensorNumerator_restrict_smul hI U a ha he d s W hWU,
    smul_comm]

end FLT.Mazur.FCurve
