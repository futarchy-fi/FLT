/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerH1Bound

/-!
# Actual inclusions between consecutive point-power section spaces

The map is the canonical divisor section tensored with the preceding power.
Its injectivity comes from the original short exact divisor sequence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Canonical inclusion from degree m sections into degree m+1 sections of the divisor line. -/
def divisorPowerH0Step (m : ℕ) :
    ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0 →ₗ[k]
      ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0 :=
  (moduleScalarHMap f (divisorTwistedComplex hI
    (tensorPower (divisorLineBundle I hI) m)).f 0).comp
      (((moduleScalarHFunctor f 0).mapIso
        (leftUnitor (tensorPower (divisorLineBundle I hI) m)).symm).toLinearEquiv.toLinearMap)

/-- The actual divisor transition is injective on degree-zero cohomology. -/
theorem divisorPowerH0Step_injective (m : ℕ) :
    Function.Injective (divisorPowerH0Step f hI m) :=
  (moduleScalarHMap_zero_injective _
    (moduleAbelianComplex_shortExact (divisorTwistedComplex_shortExact hI _
      (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m))) f).comp
        (((moduleScalarHFunctor f 0).mapIso
          (leftUnitor (tensorPower (divisorLineBundle I hI) m)).symm).toLinearEquiv.injective)

/-- The transition retains the original tensorized divisor-section map on global sections. -/
theorem divisorPowerH0Step_sections (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0) :
    moduleScalarH0Equiv f _ (divisorPowerH0Step f hI m x) =
      (divisorTwistedComplex hI (tensorPower (divisorLineBundle I hI) m)).f.app ⊤
        ((leftUnitor (tensorPower (divisorLineBundle I hI) m)).inv.app ⊤
          (moduleScalarH0Equiv f _ x)) := by
  change moduleScalarH0Equiv f _ (moduleScalarHMap f _ 0
    (moduleScalarHMap f _ 0 x)) = _
  rw [moduleScalarH0Equiv_naturality, moduleScalarH0Equiv_naturality, Iso.symm_hom]
  rfl

variable [IsProper f]

/-- The next pole quotient has exactly the difference of consecutive section dimensions. -/
theorem divisorPowerH0Step_quotient_finrank (m : ℕ) :
    Module.finrank k (ModuleScalarH f
      (tensorPower (divisorLineBundle I hI) (m + 1)) 0 ⧸
        LinearMap.range (divisorPowerH0Step f hI m)) +
      Module.finrank k (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0) =
        Module.finrank k (ModuleScalarH f
          (tensorPower (divisorLineBundle I hI) (m + 1)) 0) := by
  let _ := (hI.divisorLineBundle_locallyFreeRankOne.tensorPower (m + 1)).isFinitePresentation
  let _ := proper_coherent_hasFiniteCohomology f
    (tensorPower (divisorLineBundle I hI) (m + 1)) 0
  have he := (LinearMap.range (divisorPowerH0Step f hI m)).finrank_quotient_add_finrank
  rwa [LinearMap.finrank_range_of_inj (divisorPowerH0Step_injective f hI m)] at he

/-- A strict dimension increase supplies an actual section outside the preceding pole space. -/
theorem exists_divisorPowerH0Step_not_mem_range (m : ℕ)
    (hm : Module.finrank k (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0) <
      Module.finrank k (ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0)) :
    ∃ x, x ∉ LinearMap.range (divisorPowerH0Step f hI m) := by
  let _ := (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m).isFinitePresentation
  let _ := proper_coherent_hasFiniteCohomology f
    (tensorPower (divisorLineBundle I hI) m) 0
  by_contra! hx
  have hs : Function.Surjective (divisorPowerH0Step f hI m) := fun x ↦ hx x
  exact (not_le_of_gt hm) (LinearMap.finrank_le_finrank_of_surjective hs)

end FLT.Mazur.FCurve
