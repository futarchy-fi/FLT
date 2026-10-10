/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyReesScalars
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Original global sections of the degree-zero power cohomology sum

The H0 comparison identifies every summand with the original global sections.
The resulting Rees action on sections is induced by the original sheaf scalar
maps, with exactly the same homogeneous degrees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules)

/-- Original global sections with the specified base-ring action. -/
abbrev ringGlobalSections (N : X.Modules) : ModuleCat R :=
  (ModuleCat.restrictScalars ρ).obj (ModuleCat.of Γ(X, ⊤) Γ(N, ⊤))

/-- H0 is identified with original global sections over the specified base ring. -/
def ringHZeroSectionsEquiv (N : X.Modules) : ModuleRingH ρ N 0 ≃ₗ[R] ringGlobalSections ρ N :=
  { (moduleH0Equiv N).toAddEquiv with
    map_smul' r x := (moduleH0Equiv N).map_smul (ρ r) x }

/-- All original power sections, retaining finite degree support. -/
abbrev PowerGlobalSections := ⨁ n : ℕ, ringGlobalSections ρ (power I n M)

/-- The full H0 sum identifies degreewise with the original power sections. -/
def powerHZeroSectionsEquiv : PowerCohomologySum ρ I M 0 ≃ₗ[R] PowerGlobalSections ρ I M :=
  DirectSum.congrLinearEquiv (fun n ↦ ringHZeroSectionsEquiv ρ (power I n M))

/-- Each original H0 class stays in its own degree with its actual section. -/
lemma powerHZeroSectionsEquiv_of (n : ℕ) (x : ModuleRingH ρ (power I n M) 0) :
    powerHZeroSectionsEquiv ρ I M (DirectSum.lof R ℕ _ n x) =
      DirectSum.lof R ℕ _ n (ringHZeroSectionsEquiv ρ (power I n M) x) := by
  exact DirectSum.lmap_lof
    (fun k ↦ (ringHZeroSectionsEquiv ρ (power I k M)).toLinearMap) n x

variable [IsLocallyNoetherian X] [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- The H0 Rees action induces an action on the original global power sections. -/
@[instance_reducible]
def powerGlobalSectionsReesModule : Module (reesAlgebra J) (PowerGlobalSections ρ I M) :=
  let _ := powerReesModule ρ I M J hJ 0
  (powerHZeroSectionsEquiv ρ I M).symm.toAddEquiv.module _

/-- The degreewise H0 comparison is linear for the constructed original Rees actions. -/
def powerHZeroSectionsReesEquiv :
    let _ := powerReesModule ρ I M J hJ 0
    let _ := powerGlobalSectionsReesModule ρ I M J hJ
    PowerCohomologySum ρ I M 0 ≃ₗ[reesAlgebra J] PowerGlobalSections ρ I M :=
  let _ := powerReesModule ρ I M J hJ 0
  ((powerHZeroSectionsEquiv ρ I M).symm.toAddEquiv.linearEquiv _).symm

/-- Homogeneous shifts give precisely the actual section maps of the original scalar lifts. -/
lemma powerHZeroSections_shift_of (a n : ℕ) (r : ↥(J ^ a))
    (x : ModuleRingH ρ (power I n M) 0) :
    powerHZeroSectionsEquiv ρ I M
      (powerShift ρ I M J hJ 0 a r (DirectSum.lof R ℕ _ n x)) =
      DirectSum.lof R ℕ (fun k ↦ ringGlobalSections ρ (power I k M)) (a + n)
        ((powerScalarMap ρ I M J hJ a n r).app ⊤
          (ringHZeroSectionsEquiv ρ (power I n M) x)) := by
  rw [powerShift_of, powerHZeroSectionsEquiv_of]
  exact congrArg (DirectSum.lof R ℕ _ (a + n))
    (moduleH0Equiv_naturality (powerScalarMap ρ I M J hJ a n r) x)

end FLT.Mazur.IdealAdicQuotient
