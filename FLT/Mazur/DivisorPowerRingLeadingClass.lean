/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerLeadingClass
public import FLT.Mazur.ModuleRingCohomologyExact

/-!
# Leading classes of point powers over the original base ring

The actual divisor sequence gives injective pole transitions and exact
leading-class maps over any ring of scalars. Vanishing of the preceding
H¹ makes every leading class lift, without restricting the base to a field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} {R : Type} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The canonical pole transition, linear over the original base ring. -/
def divisorPowerRingStep (m : ℕ) :
    ModuleRingH ρ (tensorPower (divisorLineBundle I hI) m) 0 →ₗ[R]
      ModuleRingH ρ (tensorPower (divisorLineBundle I hI) (m + 1)) 0 :=
  ((moduleRingHFunctor ρ 0).map (divisorTwistedComplex hI
    (tensorPower (divisorLineBundle I hI) m)).f).hom.comp
      (((moduleRingHFunctor ρ 0).mapIso
        (leftUnitor (tensorPower (divisorLineBundle I hI) m)).symm).toLinearEquiv.toLinearMap)

/-- The actual leading class in the divisor quotient, retaining base scalars. -/
def divisorPowerRingLeading (m : ℕ) :
    ModuleRingH ρ (tensorPower (divisorLineBundle I hI) (m + 1)) 0 →ₗ[R]
      ModuleRingH ρ (divisorTwistedComplex hI
        (tensorPower (divisorLineBundle I hI) m)).X₃ 0 :=
  ((moduleRingHFunctor ρ 0).map (divisorTwistedComplex hI
    (tensorPower (divisorLineBundle I hI) m)).g).hom

/-- The original pole transition is injective over every base ring. -/
theorem divisorPowerRingStep_injective (m : ℕ) :
    Function.Injective (divisorPowerRingStep ρ hI m) :=
  (moduleRingHMap_zero_injective ρ _ (divisorTwistedComplex_shortExact hI _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m))).comp
      (((moduleRingHFunctor ρ 0).mapIso
        (leftUnitor (tensorPower (divisorLineBundle I hI) m)).symm).toLinearEquiv.injective)

/-- Vanishing of the leading class characterizes the preceding actual pole module. -/
theorem divisorPowerRingLeading_eq_zero_iff (m : ℕ)
    (x : ModuleRingH ρ (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    divisorPowerRingLeading ρ hI m x = 0 ↔
      x ∈ LinearMap.range (divisorPowerRingStep ρ hI m) := by
  have he := moduleRingH_exact_middle ρ _ (divisorTwistedComplex_shortExact hI _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)) 0 x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := he.mp hx
    let e := ((moduleRingHFunctor ρ 0).mapIso
      (leftUnitor (tensorPower (divisorLineBundle I hI) m)).symm).toLinearEquiv
    obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, hy⟩
  · rintro ⟨y, rfl⟩
    exact he.mpr ⟨_, rfl⟩

/-- Relative H¹ vanishing makes every actual leading class lift over the base ring. -/
theorem divisorPowerRingLeading_surjective (m : ℕ)
    [Subsingleton (ModuleH (tensorPower (divisorLineBundle I hI) m) 1)] :
    Function.Surjective (divisorPowerRingLeading ρ hI m) := by
  let _ : Subsingleton (ModuleRingH ρ (divisorTwistedComplex hI
      (tensorPower (divisorLineBundle I hI) m)).X₁ 1) :=
    moduleH_subsingleton_of_iso (leftUnitor _) 1
  intro x
  exact (moduleRingH_exact_right ρ _ (divisorTwistedComplex_shortExact hI _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)) 0 x).mp
      (Subsingleton.elim _ _)

/-- The actual pole filtration is exactly the kernel of the relative leading map. -/
theorem divisorPowerRingLeading_ker (m : ℕ) :
    LinearMap.ker (divisorPowerRingLeading ρ hI m) =
      LinearMap.range (divisorPowerRingStep ρ hI m) := by
  ext x
  exact divisorPowerRingLeading_eq_zero_iff ρ hI m x

/-- The positive pole quotient is the original relative divisor quotient's sections. -/
def divisorPowerRingLeadingEquiv (m : ℕ)
    [Subsingleton (ModuleH (tensorPower (divisorLineBundle I hI) m) 1)] :
    (ModuleRingH ρ (tensorPower (divisorLineBundle I hI) (m + 1)) 0 ⧸
      LinearMap.range (divisorPowerRingStep ρ hI m)) ≃ₗ[R]
        ModuleRingH ρ (divisorTwistedComplex hI
          (tensorPower (divisorLineBundle I hI) m)).X₃ 0 :=
  (Submodule.quotEquivOfEq _ _ (divisorPowerRingLeading_ker ρ hI m).symm).trans
    ((divisorPowerRingLeading ρ hI m).quotKerEquivOfSurjective
      (divisorPowerRingLeading_surjective ρ hI m))

end FLT.Mazur.FCurve
