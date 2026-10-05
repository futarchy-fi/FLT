/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection
public import FLT.Mazur.ModuleStalkExact

/-!
# The canonical effective-divisor exact sequence

The canonical map O → O(D) is injective: on each Cartier chart it is
multiplication by the regular defining equation. Its actual categorical
cokernel therefore gives a short exact sequence of module sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The canonical map on sections multiplies the canonical section by the input function. -/
lemma divisorSectionMap_app (hI : EffectiveCartier I) (U : X.Opens) (r : Γ(X, U)) :
    (divisorSectionMap hI).app U r = r • divisorSection hI U := by
  have h := Scheme.Modules.Hom.app_smul (divisorSectionMap hI) r (1 : Γ(X, U))
  simpa only [divisorSection, smul_eq_mul, mul_one] using h

/-- In Cartier coordinates the actual canonical map multiplies by the regular equation. -/
lemma divisorSectionMap_coordinate (hI : EffectiveCartier I) {U : X.affineOpens}
    (hU : CartierChart I U) (r : Γ(X, U)) :
    hU.dualEquiv (divisorChartEval I U ((divisorSectionMap hI).app U.1 r)) =
      r * hU.choose := by
  rw [divisorSectionMap_app, map_smul, map_smul, divisorSection_coordinate]
  rfl

/-- On a Cartier chart the canonical section map is injective. -/
theorem divisorSectionMap_injective_chart (hI : EffectiveCartier I) {U : X.affineOpens}
    (hU : CartierChart I U) : Function.Injective ((divisorSectionMap hI).app U.1) := by
  intro r s hrs
  apply hU.choose_spec.1.2
  exact (divisorSectionMap_coordinate hI hU r).symm.trans
    ((congrArg (fun t ↦ hU.dualEquiv (divisorChartEval I U t)) hrs).trans
      (divisorSectionMap_coordinate hI hU s))

/-- Local injectivity on regular charts gives injectivity on every open. -/
theorem divisorSectionMap_injective (hI : EffectiveCartier I) (U : X.Opens) :
    Function.Injective ((divisorSectionMap hI).app U) := by
  intro r s hrs
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨V, hxV, hVU, hV⟩ := hI.exists_chart_le hx
  refine ⟨V.1, hVU, hxV, divisorSectionMap_injective_chart hI hV ?_⟩
  have hn := (divisorSectionMap hI).mapPresheaf.naturality (homOfLE hVU).op
  exact (ConcreteCategory.congr_hom hn r).trans
    ((congrArg ((divisorLineBundle I hI).presheaf.map (homOfLE hVU).op) hrs).trans
      (ConcreteCategory.congr_hom hn s).symm)

/-- The actual canonical divisor section is a monomorphism of module sheaves. -/
instance divisorSectionMap_mono (hI : EffectiveCartier I) : Mono (divisorSectionMap hI) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective (fun U ↦ divisorSectionMap_injective hI U.unop)

/-- The canonical divisor sequence uses the actual section map and its actual cokernel. -/
def divisorSectionComplex (hI : EffectiveCartier I) : ShortComplex X.Modules :=
  ShortComplex.mk (divisorSectionMap hI) (cokernel.π (divisorSectionMap hI))
    (cokernel.condition _)

/-- The canonical divisor sequence is short exact, without properness or a field hypothesis. -/
theorem divisorSectionComplex_shortExact (hI : EffectiveCartier I) :
    (divisorSectionComplex hI).ShortExact := by
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (divisorSectionMap hI))
    (inferInstanceAs (Mono (divisorSectionMap hI)))
    (inferInstanceAs (Epi (cokernel.π (divisorSectionMap hI))))

end FLT.Mazur.FCurve
