/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPadicPowerRigidity
public import FLT.GroupScheme.RaynaudPowerPrescribedExtension

/-!
# Prescribed extension from p-power-killed models over the p-adic integers

The actual graph projection is an integral isomorphism by the derived
inertia rigidity theorem. Its inverse followed by the second projection
extends the prescribed map, and every coordinate pullback is integral.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
open NumberField IsLocalRing
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {X Y : FF ℤ_[p] ℚ_[p]}

/-- Every prescribed map from a p-power-killed model extends uniquely in small ramification. -/
theorem extend_from_padic_power (hp : 2 < p) (hX : KilledByPowerOf p X)
    (f : GenericGaloisHom X Y) : ∃! g : ModelHom X Y, genericHom g = f := by
  apply extend_of_power_rigidity p (fun {A B} hA a ha ↦ ?_) hX f
  obtain ⟨n, hn⟩ := hA
  exact ModelHom.surjective_of_padic_power p (X := A) (Y := B) hp hn a ha

/-- Coordinate pullbacks of the prescribed generic map lie in the original integral model. -/
theorem GenericGaloisHom.integral_of_padic_power (hp : 2 < p) (hX : KilledByPowerOf p X)
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[ℤ_[p]] y) = 1 ⊗ₜ[ℤ_[p]] x := by
  obtain ⟨g, hg, _⟩ := extend_from_padic_power p hp hX f
  refine ⟨g y, ?_⟩
  rw [← hg, ModelHom.toBialgHom_genericHom]
  rfl

end ThreeAdicPlan
