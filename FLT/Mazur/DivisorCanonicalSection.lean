/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleSumRestrict
public import FLT.Mazur.DivisorLineBundleSumUnit

/-!
# The canonical section of an effective Cartier divisor

Dualizing the actual ideal inclusion gives the canonical section of O(D).
On each Cartier chart its coordinate is the regular equation of D, so its
nonvanishing locus is exactly the complement of the divisor support there.
The canonical sections respect restriction and the divisor-sum comparison.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- The ideal inclusion, dualized into the positive divisor line bundle. -/
def divisorSectionMap (hI : EffectiveCartier I) :
    structureModule X ⟶ divisorLineBundle I hI :=
  moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap (idealModule I) (idealModuleι I)

/-- The canonical section on any open, as the image of the constant function one. -/
def divisorSection (hI : EffectiveCartier I) (U : X.Opens) :
    Γ(divisorLineBundle I hI, U) := (divisorSectionMap hI).app U (1 : Γ(X, U))

/-- The section is the restricted ideal inclusion followed by multiplication by one. -/
lemma divisorSection_eq (hI : EffectiveCartier I) (U : X.Opens) :
    divisorSection hI U = (Scheme.Modules.restrictFunctor U.ι).map (idealModuleι I) ≫
      moduleDualUnitSection U 1 := rfl

/-- Pairing the canonical section with an ideal element gives that element. -/
lemma divisorSection_eval (hI : EffectiveCartier I) (U : X.affineOpens)
    (s : I.ideal U) : divisorChartEval I U (divisorSection hI U.1) s = s := by
  change moduleDualEval (idealModule I) U.1 (divisorSection hI U.1)
    ((idealModuleAffineEquiv I U).symm s) = _
  rw [divisorSection_eq, moduleDualEval_precomp, moduleDualEval_unitSection, one_mul,
    ← idealModuleAffineEquiv_val, LinearEquiv.apply_symm_apply]

/-- The canonical sections on different opens are restrictions of one another. -/
lemma divisorSection_restrict (hI : EffectiveCartier I) {U V : X.Opens} (h : V ≤ U) :
    (divisorLineBundle I hI).presheaf.map (CategoryTheory.homOfLE h).op
      (divisorSection hI U) = divisorSection hI V := by
  have hn := congrArg (fun k ↦ k (1 : Γ(X, U)))
    ((divisorSectionMap hI).mapPresheaf.naturality (CategoryTheory.homOfLE h).op)
  change (divisorSectionMap hI).app V (X.presheaf.map (CategoryTheory.homOfLE h).op 1) =
    (divisorLineBundle I hI).presheaf.map (CategoryTheory.homOfLE h).op
      (divisorSection hI U) at hn
  simpa only [map_one, divisorSection] using hn.symm

/-- The coordinate of the canonical section is the chosen regular local equation. -/
lemma divisorSection_coordinate (hI : EffectiveCartier I) {U : X.affineOpens}
    (hU : CartierChart I U) :
    hU.dualEquiv (divisorChartEval I U (divisorSection hI U.1)) = hU.choose := by
  change divisorChartEval I U (divisorSection hI U.1) (hU.idealEquiv 1) = _
  rw [divisorSection_eval]
  change 1 * hU.choose = hU.choose
  exact one_mul _

/-- The canonical section cuts out the original ideal on every Cartier chart. -/
lemma divisorSection_span (hI : EffectiveCartier I) {U : X.affineOpens}
    (hU : CartierChart I U) :
    Ideal.span {hU.dualEquiv (divisorChartEval I U (divisorSection hI U.1))} = I.ideal U := by
  rw [divisorSection_coordinate]
  exact hU.choose_spec.2.symm

/-- On a Cartier chart, the section is nonvanishing precisely off the divisor support. -/
lemma divisorSection_nonvanishing (hI : EffectiveCartier I) {U : X.affineOpens}
    (hU : CartierChart I U) {x : X} (hx : x ∈ U.1) :
    x ∈ X.basicOpen (hU.dualEquiv (divisorChartEval I U (divisorSection hI U.1))) ↔
      x ∉ I.support := by
  rw [divisorSection_coordinate, I.mem_support_iff_of_mem hx]
  conv_rhs => rw [hU.choose_spec.2, X.zeroLocus_span, X.zeroLocus_singleton]
  simp

/-- Adding divisors multiplies their canonical sections under the actual sum comparison. -/
lemma divisorSection_sum (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (U : X.affineOpens) (hU : CartierChart I U) (hV : CartierChart J U) :
    (divisorLineBundleSumIso hI hJ).hom.app U.1
      (ModuleSheafTensor.pure _ _ U.1 (divisorSection hI U.1) (divisorSection hJ U.1)) =
        divisorSection (hI.mul hJ) U.1 := by
  apply (hU.mul hV).divisorChartEval_bijective.injective
  apply hU.dual_ext_products hV
  intro x y
  rw [divisorLineBundleSumIso_eval hI hJ U hU hV]
  simp only [divisorSection_eval]

end FLT.Mazur.FCurve
