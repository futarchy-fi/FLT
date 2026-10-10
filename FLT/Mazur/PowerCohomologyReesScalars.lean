/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyReesAction

/-!
# Original base scalars inside the cohomological Rees action

The constructed Rees module restricts to the original R-module structure
on every cohomology summand. This supplies the scalar tower needed for
geometric comparisons without replacing the original coefficient action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower FLT.Mazur.IdealPowerScalarLift
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)
  (q : ℕ)

/-- A degree-zero lift is the original scalar map, with its canonical degree transport. -/
lemma powerScalarMap_zero (n : ℕ) (r : R) :
    powerScalarMap ρ I M J hJ 0 n ⟨r, by simp⟩ =
      scalarEnd (power I n M) (ρ r) ≫ powerReindex I M (Nat.zero_add n).symm := by
  apply (cancel_mono (inclusion (I ^ (0 + n)) M)).mp
  rw [powerScalarMap_inclusion, Category.assoc,
    powerTransport_inclusion I M (Nat.zero_add n).symm]

omit [IsLocallyNoetherian X] in
/-- Cohomology of an original scalar endomorphism is the specified base action. -/
lemma moduleRingH_scalarEnd (N : X.Modules) (r : R) (x : ModuleRingH ρ N q) :
    ((moduleRingHFunctor ρ q).map (scalarEnd N (ρ r))).hom x = r • x := rfl

/-- The degree-zero shift is ordinary scalar multiplication on the full sum. -/
lemma powerShift_zero (r : R) :
    powerShift ρ I M J hJ q 0 ⟨r, by simp⟩ =
      r • (1 : Module.End R (PowerCohomologySum ρ I M q)) := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  change powerShift ρ I M J hJ q 0 _ (DirectSum.lof R ℕ _ n x) =
    r • DirectSum.lof R ℕ _ n x
  rw [powerShift_of, powerScalarMap_zero, Functor.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, powerCohomology_transport]
  rw [moduleRingH_scalarEnd]
  exact (DirectSum.lof R ℕ (fun k ↦ ModuleRingH ρ (power I k M) q) n).map_smul r x

/-- Constants in the Rees algebra act by the unchanged base-ring action. -/
lemma powerReesModule_algebraMap_smul (r : R) (x : PowerCohomologySum ρ I M q) :
    let _ := powerReesModule ρ I M J hJ q
    algebraMap R (reesAlgebra J) r • x = r • x := by
  change powerReesRepresentation ρ I M J hJ q (algebraMap R (reesAlgebra J) r) x = _
  have h : algebraMap R (reesAlgebra J) r = Rees.monomial J 0 ⟨r, by simp⟩ :=
    Subtype.ext rfl
  rw [h, powerReesRepresentation_monomial, powerShift_zero]
  rfl

/-- The genuine Rees action extends the original base scalars. -/
theorem powerReesScalarTower :
    let _ := powerReesModule ρ I M J hJ q
    IsScalarTower R (reesAlgebra J) (PowerCohomologySum ρ I M q) := by
  let _ := powerReesModule ρ I M J hJ q
  exact IsScalarTower.of_algebraMap_smul
    (powerReesModule_algebraMap_smul ρ I M J hJ q)

end FLT.Mazur.IdealAdicQuotient
