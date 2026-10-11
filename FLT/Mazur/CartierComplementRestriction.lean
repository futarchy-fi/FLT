/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts

/-!
# Cartier complements detect regular functions

Localization at a regular equation is injective. Checking on Cartier charts
therefore proves faithful restriction on every open, without reducedness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- A local defining equation is invertible only off the divisor support. -/
theorem cartierEquation_basicOpen_le_complement {U : X.affineOpens}
    {a : Γ(X, U)} (he : I.ideal U = Ideal.span {a}) :
    X.basicOpen a ≤ I.support.compl := by
  intro x hx hs
  have hz := (I.mem_support_iff_of_mem (X.basicOpen_le a hx)).mp hs
  rw [he, X.zeroLocus_span, X.zeroLocus_singleton] at hz
  exact hz hx

/-- Restriction to the principal open of a regular element is injective. -/
theorem regular_basicOpen_restrict_injective {U : X.affineOpens}
    {a : Γ(X, U)} (ha : IsRegular a) :
    Function.Injective (X.presheaf.map (homOfLE (X.basicOpen_le a)).op) := by
  let _ := U.2.isLocalization_basicOpen a
  exact IsLocalization.injective Γ(X, X.basicOpen a)
    (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp ha))

/-- Restricting functions to the Cartier complement loses no section. -/
theorem cartierComplement_restrict_injective (hI : EffectiveCartier I) (W : X.Opens) :
    Function.Injective (X.presheaf.map
      (homOfLE (show W ⊓ I.support.compl ≤ W from inf_le_left)).op) := by
  intro s t he
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨U, hxU, hUW, a, ha, hUa⟩ := hI.exists_chart_le hx
  refine ⟨U.1, hUW, hxU, regular_basicOpen_restrict_injective ha ?_⟩
  have hb : X.basicOpen a ≤ W ⊓ I.support.compl :=
    le_inf ((X.basicOpen_le a).trans hUW) (cartierEquation_basicOpen_le_complement hUa)
  have hh := congrArg (X.presheaf.map (homOfLE hb).op) he
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, homOfLE_comp] using hh

end FLT.Mazur.FCurve
