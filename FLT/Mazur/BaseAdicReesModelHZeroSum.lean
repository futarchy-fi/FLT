/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelGlobalSections
public import FLT.Mazur.PowerCohomologyHZeroSections

/-!
# Degree-zero cohomology of the actual direct image

Global section coordinates give the H0/direct-sum comparison for the original
ideal-power sheaves. The comparison preserves any specified source base-ring
map, and agrees degreewise with the original H0-to-sections equivalences.
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
  {A : Type u} [CommRing A] (ρ : A →+* Γ(X, ⊤))

attribute [local irreducible] modelPushforward modelPointwiseSumIso

/-- Global coordinates retain any specified source base-ring action. -/
def modelPowerGlobalSectionsEquiv :
    ringGlobalSections ρ (modelPushforward f J M) ≃ₗ[A]
      PowerGlobalSections ρ ((baseIdeal R J).comap f) M :=
  { (modelPowerSectionsEquiv f J M ⊤).toAddEquiv with
    map_smul' := fun r s ↦ (modelPowerSectionsEquiv f J M ⊤).map_smul (ρ r) s }

/-- H0 of the actual direct image is the sum of the original ideal-power H0 groups. -/
def modelPowerHZeroEquiv :
    ModuleRingH ρ (modelPushforward f J M) 0 ≃ₗ[A]
      PowerCohomologySum ρ ((baseIdeal R J).comap f) M 0 :=
  (ringHZeroSectionsEquiv ρ (modelPushforward f J M)).trans
    ((modelPowerGlobalSectionsEquiv f J M ρ).trans
      (powerHZeroSectionsEquiv ρ ((baseIdeal R J).comap f) M).symm)

/-- The H0 sum comparison has exactly the original global section coordinates. -/
lemma modelPowerHZeroEquiv_sections (s : ModuleRingH ρ (modelPushforward f J M) 0) :
    powerHZeroSectionsEquiv ρ ((baseIdeal R J).comap f) M
        (modelPowerHZeroEquiv f J M ρ s) =
      modelPowerGlobalSectionsEquiv f J M ρ
        (ringHZeroSectionsEquiv ρ (modelPushforward f J M) s) :=
  (powerHZeroSectionsEquiv ρ ((baseIdeal R J).comap f) M).apply_symm_apply _

/-- Every original degree's H0 class recovers its actual global section. -/
lemma modelPowerHZeroEquiv_degree (s : ModuleRingH ρ (modelPushforward f J M) 0) (n : ℕ) :
    ringHZeroSectionsEquiv ρ (modelPowerSheaves f J M n)
        (modelPowerHZeroEquiv f J M ρ s n) =
      modelPowerSectionsEquiv f J M ⊤
        (ringHZeroSectionsEquiv ρ (modelPushforward f J M) s) n := by
  exact congrArg (fun t : PowerGlobalSections ρ ((baseIdeal R J).comap f) M ↦ t n)
    (modelPowerHZeroEquiv_sections f J M ρ s)

end FLT.Mazur.BaseAdicRees
