/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerHZeroTransition

/-!
# Leading classes in the actual divisor quotient

The quotient morphism of the tensorized divisor sequence detects exactly
which sections lie in the preceding pole space. When that preceding power
has vanishing first cohomology, every leading class is attained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The leading class is induced by the original divisor quotient morphism. -/
def divisorPowerLeadingClass (m : ℕ) :
    ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0 →ₗ[k]
      ModuleScalarH f (divisorTwistedComplex hI
        (tensorPower (divisorLineBundle I hI) m)).X₃ 0 :=
  moduleScalarHMap f (divisorTwistedComplex hI
    (tensorPower (divisorLineBundle I hI) m)).g 0

/-- A leading class vanishes exactly on the preceding canonical pole space. -/
theorem divisorPowerLeadingClass_eq_zero_iff (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    divisorPowerLeadingClass f hI m x = 0 ↔
      x ∈ LinearMap.range (divisorPowerH0Step f hI m) := by
  have he := moduleScalarH_exact₂ _
    (moduleAbelianComplex_shortExact (divisorTwistedComplex_shortExact hI _
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m))) f 0 x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := he.mp hx
    let e := ((moduleScalarHFunctor f 0).mapIso
      (leftUnitor (tensorPower (divisorLineBundle I hI) m)).symm).toLinearEquiv
    obtain ⟨z, rfl⟩ := e.surjective y
    exact ⟨z, hy⟩
  · rintro ⟨y, rfl⟩
    exact he.mpr ⟨_, rfl⟩

/-- Exact poles are precisely the sections with nonzero actual leading class. -/
theorem divisorPowerLeadingClass_ne_zero_iff (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    divisorPowerLeadingClass f hI m x ≠ 0 ↔
      x ∉ LinearMap.range (divisorPowerH0Step f hI m) :=
  not_congr (divisorPowerLeadingClass_eq_zero_iff f hI m x)

/-- Vanishing of the preceding first cohomology makes all leading classes attainable. -/
theorem divisorPowerLeadingClass_surjective (m : ℕ)
    [Subsingleton (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 1)] :
    Function.Surjective (divisorPowerLeadingClass f hI m) := by
  let e : ModuleScalarH f (divisorTwistedComplex hI
      (tensorPower (divisorLineBundle I hI) m)).X₁ 1 ≃ₗ[k]
        ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 1 :=
    ((moduleScalarHFunctor f 1).mapIso
    (leftUnitor (tensorPower (divisorLineBundle I hI) m))).toLinearEquiv
  let _ := e.injective.subsingleton
  intro x
  exact (moduleScalarH_exact₃ _
    (moduleAbelianComplex_shortExact (divisorTwistedComplex_shortExact hI _
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m))) f 0 x).mp
        (Subsingleton.elim _ _)

/-- The original pole transition is exactly the kernel of the leading map. -/
theorem divisorPowerLeadingClass_ker (m : ℕ) :
    LinearMap.ker (divisorPowerLeadingClass f hI m) =
      LinearMap.range (divisorPowerH0Step f hI m) := by
  ext x
  exact divisorPowerLeadingClass_eq_zero_iff f hI m x

/-- The positive pole quotient is canonically the actual divisor quotient's section space. -/
def divisorPowerLeadingEquiv (m : ℕ)
    [Subsingleton (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 1)] :
    (ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0 ⧸
      LinearMap.range (divisorPowerH0Step f hI m)) ≃ₗ[k]
        ModuleScalarH f (divisorTwistedComplex hI
          (tensorPower (divisorLineBundle I hI) m)).X₃ 0 :=
  (Submodule.quotEquivOfEq _ _ (divisorPowerLeadingClass_ker f hI m).symm).trans
    ((divisorPowerLeadingClass f hI m).quotKerEquivOfSurjective
      (divisorPowerLeadingClass_surjective f hI m))

/-- The quotient identification retains the original leading-class map on every section. -/
theorem divisorPowerLeadingEquiv_mk (m : ℕ)
    [Subsingleton (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 1)]
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    divisorPowerLeadingEquiv f hI m (Submodule.Quotient.mk x) =
      divisorPowerLeadingClass f hI m x := by
  rw [divisorPowerLeadingEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

end FLT.Mazur.FCurve
