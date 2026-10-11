/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerLeadingClass
public import FLT.Mazur.DivisorTwistedProjection
public import FLT.Mazur.ModuleDirectImageHZero

/-!
# Leading classes as sections of the actual restricted line

The tensorized divisor cokernel is identified with the original line power
restricted to the closed divisor. The comparison retains the base-field
action and the original quotient morphism on every global section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Leading classes are canonically H0 of the original power restricted to the divisor. -/
def divisorLeadingRestrictionEquiv (m : ℕ) :
    ModuleScalarH f (divisorTwistedComplex hI
      (tensorPower (divisorLineBundle I hI) m)).X₃ 0 ≃ₗ[k]
    ModuleScalarH (I.subschemeι ≫ f) ((pullback I.subschemeι).obj
      (tensorPower (divisorLineBundle I hI) (m + 1))) 0 :=
  (((moduleScalarHFunctor f 0).mapIso (divisorTwistedQuotientIso hI _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m))).toLinearEquiv).trans
      (moduleDirectImageH0Equiv I.subschemeι f (I.subschemeι ≫ f) rfl _)

/-- The actual quotient map gives a section of the restricted original line power. -/
def divisorPowerRestrictedLeading (m : ℕ) :
    ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0 →ₗ[k]
      ModuleScalarH (I.subschemeι ≫ f) ((pullback I.subschemeι).obj
        (tensorPower (divisorLineBundle I hI) (m + 1))) 0 :=
  (divisorLeadingRestrictionEquiv f hI m).toLinearMap.comp (divisorPowerLeadingClass f hI m)

/-- The restricted leading section is the original quotient morphism followed by its comparison. -/
theorem divisorPowerRestrictedLeading_sections (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    moduleScalarH0Equiv (I.subschemeι ≫ f) _ (divisorPowerRestrictedLeading f hI m x) =
      (divisorTwistedQuotientIso hI _
        (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)).hom.app ⊤
          ((divisorTwistedComplex hI (tensorPower (divisorLineBundle I hI) m)).g.app ⊤
            (moduleScalarH0Equiv f _ x)) := by
  unfold divisorPowerRestrictedLeading divisorLeadingRestrictionEquiv
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply]
  erw [moduleDirectImageH0Equiv_sections]
  change moduleScalarH0Equiv f _ (moduleScalarHMap f _ 0
    (moduleScalarHMap f _ 0 x)) = _
  rw [moduleScalarH0Equiv_naturality, moduleScalarH0Equiv_naturality]
  rfl

/-- The leading section is the actual pullback of the original global section. -/
theorem divisorPowerRestrictedLeading_pullGlobal (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    moduleScalarH0Equiv (I.subschemeι ≫ f) _ (divisorPowerRestrictedLeading f hI m x) =
      pullGlobal I.subschemeι _ (moduleScalarH0Equiv f _ x) := by
  rw [divisorPowerRestrictedLeading_sections]
  exact congrArg (fun g ↦ g.app ⊤ (moduleScalarH0Equiv f _ x))
    (divisorTwistedQuotientIso_projection hI (tensorPower (divisorLineBundle I hI) m)
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m))

/-- The actual restricted leading section vanishes precisely on the original lower pole space. -/
theorem divisorPowerRestrictedLeading_eq_zero_iff (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    divisorPowerRestrictedLeading f hI m x = 0 ↔
      x ∈ LinearMap.range (divisorPowerH0Step f hI m) := by
  change divisorLeadingRestrictionEquiv f hI m (divisorPowerLeadingClass f hI m x) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, divisorPowerLeadingClass_eq_zero_iff]

/-- Positive H1 vanishing realizes every section of the restricted original line power. -/
theorem divisorPowerRestrictedLeading_surjective (m : ℕ)
    [Subsingleton (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 1)] :
    Function.Surjective (divisorPowerRestrictedLeading f hI m) :=
  (divisorLeadingRestrictionEquiv f hI m).surjective.comp
    (divisorPowerLeadingClass_surjective f hI m)

end FLT.Mazur.FCurve
