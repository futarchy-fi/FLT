/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyScalarMaps

/-!
# High-degree scalars kill inclusion kernels after reduction

A scalar of degree at least b factors through the b-th power already on the
original coefficient sheaf. Its action on an inclusion kernel therefore
vanishes after transition to that power, in every cohomological degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility FLT.Mazur.IdealPowerScalarLift

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- High homogeneous scalars factor through the lower power on the original coefficient. -/
lemma powerScalarMap_transition_factor (a b n : ℕ) (hba : b ≤ a) (r : ↥(J ^ a)) :
    powerScalarMap ρ I M J hJ a n r ≫
        transition I M (hba.trans (Nat.le_add_right a n)) =
      inclusion (I ^ n) M ≫ scalarLift (I ^ b) M (ρ r)
        (basePowerScalar_mem ρ I J hJ b r (Ideal.pow_le_pow_right hba r.property)) := by
  apply (cancel_mono (inclusion (I ^ b) M)).mp
  rw [Category.assoc, transition_comp, powerScalarMap_inclusion,
    Category.assoc, scalarLift_inclusion, scalarEnd_naturality]

/-- A high homogeneous action on an actual inclusion kernel dies after lower reduction. -/
lemma powerScalarMap_kernel_transition_zero (q a b n : ℕ) (hba : b ≤ a)
    (r : ↥(J ^ a)) (x : ModuleRingH ρ (power I n M) q)
    (hx : moduleHMap (inclusion (I ^ n) M) q x = 0) :
    moduleHMap (transition I M (hba.trans (Nat.le_add_right a n))) q
      (moduleHMap (powerScalarMap ρ I M J hJ a n r) q x) = 0 := by
  rw [← LinearMap.comp_apply, ← moduleHMap_comp,
    powerScalarMap_transition_factor ρ I M J hJ a b n hba r]
  rw [moduleHMap_comp, LinearMap.comp_apply, hx, map_zero]

end FLT.Mazur.IdealAdicQuotient
