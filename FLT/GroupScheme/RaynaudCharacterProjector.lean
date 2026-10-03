/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudAugmentationAction

/-!
# Character projectors by twisted averaging

A character eigenspace is defined by its eigenvalue equations. Twisting the
representation by the inverse character identifies it with an invariant
submodule, so Mathlib's averaging construction supplies its projection.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
namespace CharacterProjector

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  (ρ : Representation R G V) (χ : G →* Rˣ)

/-- Twist the actual action by the inverse character. -/
def twist : Representation R G V where
  toFun g := (↑(χ g)⁻¹ : R) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp [smul_smul, mul_comm, Module.End.mul_apply]

/-- The character eigenspace, constructed as the invariants of the twist. -/
def eigenspace : Submodule R V := (twist ρ χ).invariants

/-- Membership is exactly the prescribed scalar-character equation. -/
theorem mem_eigenspace_iff (v : V) :
    v ∈ eigenspace ρ χ ↔ ∀ g, ρ g v = (χ g : R) • v := by
  constructor
  · intro hv g
    have h := congrArg ((χ g : R) • ·) (hv g)
    simpa [twist, smul_smul] using h
  · intro hv g
    change (↑(χ g)⁻¹ : R) • ρ g v = v
    rw [hv, smul_smul]
    simp

variable [Fintype G] [Invertible (Fintype.card G : R)]

/-- The normalized character-weighted average on the original module. -/
def projector : V →ₗ[R] V := (twist ρ χ).averageMap

/-- The average is a projection onto the eigenspace derived from the action. -/
theorem isProj_projector : LinearMap.IsProj (eigenspace ρ χ) (projector ρ χ) :=
  (twist ρ χ).isProj_averageMap

/-- Every projected vector satisfies the character equation. -/
theorem projector_mem (v : V) : projector ρ χ v ∈ eigenspace ρ χ :=
  (twist ρ χ).averageMap_invariant v

/-- The projector fixes every vector of its eigenspace. -/
theorem projector_eq_self (v : V) (hv : v ∈ eigenspace ρ χ) :
    projector ρ χ v = v := (twist ρ χ).averageMap_id v hv

/-- Applying the projector twice has the same effect as applying it once. -/
theorem projector_idempotent : (projector ρ χ).comp (projector ρ χ) = projector ρ χ := by
  ext v
  exact projector_eq_self ρ χ _ (projector_mem ρ χ v)

/-- Explicit finite-sum formula for the projector. -/
theorem projector_apply (v : V) :
    projector ρ χ v = ⅟(Fintype.card G : R) •
      ∑ g : G, (↑(χ g)⁻¹ : R) • ρ g v := by
  simp [projector, Representation.averageMap, GroupAlgebra.average, twist]

end CharacterProjector
end ThreeAdicPlan
