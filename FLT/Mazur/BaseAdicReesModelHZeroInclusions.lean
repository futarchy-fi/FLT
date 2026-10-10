/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelHZeroSum
public import FLT.Mazur.NoetherianModuleSumInclusions

/-!
# The H0 comparison preserves the original degree maps

The global section and H0 comparisons carry each actual ideal-power inclusion
into the corresponding direct-sum degree, with no change of representatives.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.FCurve
open FLT.Mazur.IdealAdicQuotient
open scoped DirectSum

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X]
  (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPushforward modelPushforwardPowerSectionsIso

/-- The actual degree inclusion is the original sectionwise inclusion under the global iso. -/
lemma modelPowerInclusion_pointwiseSum (n : ℕ) :
    modelPowerInclusion f J M n ≫ (modelPointwiseSumIso f J M).hom =
      NoetherianModuleSum.inclusion (modelPowerSheaves f J M) n := by
  apply AffineBasisModuleMorphism.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change (modelPointwiseSumIso f J M).hom.app U.1
    ((modelPowerInclusion f J M n).app U.1 s) = _
  rw [modelPointwiseSumIso_hom_app]
  change (modelPushforwardPowerSectionsIso f J M U).hom
    ((AffineBasisSumMaps.ι _ _ (modelPowerBasisIso f J M) _ n).app U.1 s) = _
  rw [AffineBasisSumMaps.ι_app]
  exact (modelPushforwardPowerSectionsIso f J M U).inv_hom_id_apply _

/-- The original degree inclusion has the original single-coordinate formula on every open. -/
lemma modelPowerSectionsEquiv_inclusion (n : ℕ) (U : X.Opens)
    (s : Γ(modelPowerSheaves f J M n, U)) :
    modelPowerSectionsEquiv f J M U ((modelPowerInclusion f J M n).app U s) =
      DirectSum.of (fun k ↦ Γ(modelPowerSheaves f J M k, U)) n s :=
  ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app U) (modelPowerInclusion_pointwiseSum f J M n)) s

/-- H0 of the actual degree inclusion is exactly the corresponding direct-sum inclusion. -/
lemma modelPowerHZeroEquiv_inclusion {A : Type u} [CommRing A]
    (ρ : A →+* Γ(X, ⊤)) (n : ℕ) (s : ModuleRingH ρ (modelPowerSheaves f J M n) 0) :
    modelPowerHZeroEquiv f J M ρ (moduleHMap (modelPowerInclusion f J M n) 0 s) =
      DirectSum.lof A ℕ _ n s := by
  apply (powerHZeroSectionsEquiv ρ ((baseIdeal R J).comap f) M).injective
  rw [modelPowerHZeroEquiv_sections, powerHZeroSectionsEquiv_of]
  change modelPowerSectionsEquiv f J M ⊤
      (moduleH0Equiv (modelPushforward f J M)
        (moduleHMap (modelPowerInclusion f J M n) 0 s)) = _
  rw [moduleH0Equiv_naturality, modelPowerSectionsEquiv_inclusion]
  rfl

end FLT.Mazur.BaseAdicRees
