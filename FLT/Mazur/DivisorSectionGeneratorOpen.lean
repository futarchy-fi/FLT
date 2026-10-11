/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorSectionComplement
public import FLT.Mazur.ModuleSectionRatioOpen

/-!
# The canonical section's generator open is the divisor complement

On a generating Cartier chart, surjectivity of the section map makes the
original local equation a unit. Conversely the canonical section already
trivializes the actual divisor complement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The canonical divisor section generates exactly away from the original divisor. -/
theorem divisorSection_generatorOpen :
    sectionGeneratorOpen (divisorLineBundle I hI) (divisorSection hI ⊤) = I.support.compl := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU, hC⟩ := hI.exists_chart_le hx
    let e := (hC.divisorSectionsEquiv hI).trans hC.dualEquiv
    let _ := sectionGeneratorOpen_app_isIso _ (divisorSection hI ⊤) U.1 hU
    obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso
      ((globalSectionHom (divisorLineBundle I hI) (divisorSection hI ⊤)).app U.1)).surjective
        (e.symm (1 : Γ(X, U.1)))
    change Γ(X, U.1) at r
    change r • (divisorLineBundle I hI).presheaf.map U.1.leTop.op
      (divisorSection hI ⊤) = e.symm 1 at hr
    erw [divisorSection_restrict hI (show U.1 ≤ ⊤ from le_top)] at hr
    have he := congrArg e hr
    rw [e.map_smul, LinearEquiv.apply_symm_apply] at he
    change r * hC.dualEquiv (divisorChartEval I U (divisorSection hI U.1)) = 1 at he
    rw [divisorSection_coordinate] at he
    have hu : I.ideal U = ⊤ := by
      rw [hC.choose_spec.2, Ideal.span_singleton_eq_top]
      exact IsUnit.of_mul_eq_one_right r he
    change x ∉ I.support
    rw [I.mem_support_iff_of_mem hxU, hu]
    change x ∉ X.zeroLocus (U := U.1) Set.univ
    rw [X.zeroLocus_univ]
    exact fun h ↦ h hxU
  · let _ := divisorSection_isIso_complement hI
    have hi : IsIso (sectionHom (divisorLineBundle I hI) I.support.compl
        ((divisorLineBundle I hI).presheaf.map (homOfLE le_top).op
          (divisorSection hI ⊤))) := by
      rw [divisorSection_restrict]
      infer_instance
    exact le_sectionGeneratorOpen _ _ _

end FLT.Mazur.FCurve
