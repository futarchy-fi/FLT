/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementCanonical
public import FLT.Mazur.DivisorFunctionalScalar
public import FLT.Mazur.DivisorPowerCanonicalSection

/-!
# The original tensor numerator recovers its complement function

Cancel the actual divisor-power comparison, preserving the canonical section,
then take the canonical local coordinate on the complement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
open GlobalIdealPowerCompatibility ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Cancel the original divisor-power comparison in a local numerator formula. -/
theorem divisorTensorNumerator_restrict (U : X.Opens) (m : ℕ)
    (t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)) (r : Γ(X, U))
    (ht : (divisorLineBundle (I ^ m) (hI.pow m)).presheaf.map U.leTop.op
      ((divisorLineBundlePowerIso hI m).hom.app ⊤ t) = r • divisorSection (hI.pow m) U) :
    (tensorPower (divisorLineBundle I hI) m).presheaf.map U.leTop.op t =
      r • tensorPowerSection (divisorLineBundle I hI) U (divisorSection hI U) m := by
  apply (ConcreteCategory.bijective_of_isIso
    ((divisorLineBundlePowerIso hI m).hom.app U)).injective
  rw [Hom.app_smul, divisorSection_power]
  have hn := congrArg (fun f ↦ f t)
    ((divisorLineBundlePowerIso hI m).hom.mapPresheaf.naturality U.leTop.op)
  exact hn.trans ht

/-- A local scalar multiple of the canonical power has that scalar as its function. -/
theorem divisorComplementFunction_of_restrict (m : ℕ)
    (t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)) (r : Γ(X, complement I))
    (ht : (tensorPower (divisorLineBundle I hI) m).presheaf.map (complement I).leTop.op t =
      r • tensorPowerSection (divisorLineBundle I hI) (complement I)
        (divisorSection hI (complement I)) m) :
    divisorComplementFunction hI m t = (complement I).topIso.inv r := by
  let U := complement I
  let M := tensorPower (divisorLineBundle I hI) m
  have hr := congrArg (M.presheaf.map (homOfLE (le_of_eq U.ι_image_top)).op) ht
  rw [Scheme.Modules.map_smul, tensorPowerSection_restrict, divisorSection_restrict] at hr
  rw [← Functor.map_comp_apply] at hr
  change M.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op t = _ at hr
  dsimp only [M, U] at hr
  have hc := divisorComplementFunction_power hI m
  unfold divisorComplementFunction at hc ⊢
  rw [tensorPowerSection_restrict, divisorSection_restrict] at hc
  rw [hr, SectionGradedLocalCoordinates.coordinate_smul, hc, mul_one]
  rfl

/-- The ideal-dual multiplication formula identifies the actual numerator function. -/
theorem divisorComplementFunction_of_numerator (m : ℕ)
    (t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤))
    (a : Γ((complement I).toScheme, ⊤))
    (ht : (divisorLineBundle (I ^ m) (hI.pow m)).presheaf.map (complement I).leTop.op
      ((divisorLineBundlePowerIso hI m).hom.app ⊤ t) =
      (restrictFunctor (complement I).ι).map (idealModuleι (I ^ m)) ≫
        IdealPowerScalarLift.scalarEnd ((structureModule X).restrict (complement I).ι) a ≫
          moduleDualUnitSection (complement I) 1) :
    divisorComplementFunction hI m t = a := by
  let r := (complement I).topIso.hom a
  have ha : (complement I).topIso.inv r = a :=
    ConcreteCategory.congr_hom (complement I).topIso.hom_inv_id a
  rw [← ha, divisorFunctionalScalar_eq (hI.pow m)] at ht
  exact (divisorComplementFunction_of_restrict hI m t r
    (divisorTensorNumerator_restrict hI (complement I) m t r ht)).trans ha

end FLT.Mazur.FCurve
