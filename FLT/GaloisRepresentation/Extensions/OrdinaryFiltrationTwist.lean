/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationBasis

/-!
# Simultaneous twists of actual ordinary filtrations

The scalar twist is constructed on the middle representation and both line
characters. Its normalized difference is unchanged, so its extracted class
is the existing identity transport of ordinary Hom coefficients.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.Extensions

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (ψ : G →* kˣ)

/-- Scalar twist of the actual middle representation. -/
def ordinaryTwistRepresentation : Representation k G V where
  toFun g := (ψ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply,
      map_smul, smul_smul]
    rw [mul_comm (ψ g : k) (ψ h : k)]

namespace OrdinaryFiltration

variable {ρ} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)

/-- Twisting both lines preserves the same exact underlying sequence. -/
def twist : OrdinaryFiltration (ordinaryTwistRepresentation ρ ψ) (α * ψ) (β * ψ) where
  injection := E.injection
  projection := E.projection
  injective := E.injective
  surjective := E.surjective
  exact := E.exact
  injection_equivariant g x := by
    change (ψ g : k) • ρ g (E.injection x) = E.injection (((α * ψ) g : kˣ) * x)
    rw [E.injection_equivariant, ← map_smul]
    congr 1
    simp only [smul_eq_mul, MonoidHom.mul_apply, Units.val_mul]
    ring
  projection_equivariant g x := by
    change E.projection ((ψ g : k) • ρ g x) = (((β * ψ) g : kˣ) : k) * E.projection x
    rw [map_smul, E.projection_equivariant]
    simp only [smul_eq_mul, MonoidHom.mul_apply, Units.val_mul]
    ring

variable [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
    [TopologicalSpace V] [DiscreteTopology V]
    (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))
    (hψ : Continuous (fun g : G ↦ (ψ g : k)))

include hρ hψ in
/-- The constructed twist is continuous on every orbit. -/
theorem continuous_twistOrbit (x : V) :
    Continuous (fun g : G ↦ ordinaryTwistRepresentation ρ ψ g x) :=
  (continuous_of_discreteTopology : Continuous (fun t : k × V ↦ t.1 • t.2)).comp
    (hψ.prodMk (hρ x))

/-- The normalized actual cocycle is unchanged by a simultaneous twist. -/
theorem cocycleOf_twist (w : V) (hw : E.projection w = 1) :
    (E.twist ψ).cocycleOf (continuous_twistOrbit ψ hρ hψ) w hw =
      mapCoefficientCocycle (ordinaryHomTwistEquiv α β ψ)
        (ordinaryHomTwistEquiv_equivariant α β ψ) (E.cocycleOf hρ w hw) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  apply LinearMap.ext_ring
  apply E.injective
  change (E.twist ψ).injection _ = E.injection _
  rw [(E.twist ψ).cocycleOf_spec (continuous_twistOrbit ψ hρ hψ) w hw g]
  change _ = E.injection ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).1 g) 1)
  rw [E.cocycleOf_spec hρ]
  change (((β * ψ) g : kˣ) : k)⁻¹ • ((ψ g : k) • ρ g w) - w = _
  simp [smul_smul, mul_inv_rev, mul_comm]

/-- The class of the actual twist is the identity transport on Hom coefficients. -/
theorem extensionClass_twist :
    (E.twist ψ).extensionClass (continuous_twistOrbit ψ hρ hψ) =
      mapCoefficientClass (ordinaryHomTwistEquiv α β ψ)
        (ordinaryHomTwistEquiv_equivariant α β ψ) (E.extensionClass hρ) := by
  obtain ⟨w, hw⟩ := E.surjective 1
  rw [(E.twist ψ).extensionClass_eq (continuous_twistOrbit ψ hρ hψ) w hw,
    E.extensionClass_eq hρ w hw, E.cocycleOf_twist ψ hρ hψ w hw]
  rfl

end OrdinaryFiltration

end GaloisRepresentation.Extensions
