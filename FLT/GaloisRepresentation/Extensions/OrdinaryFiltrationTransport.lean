/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationBasis

/-!
# Transport of an actual ordinary filtration

A linear intertwiner transports the exact sequence and preserves its extracted
normalized cocycle and extension class. No class is chosen as filtration data.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions.OrdinaryFiltration
variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
  {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β) (e : V ≃ₗ[k] W)
  (he : ∀ g x, σ g (e x) = e (ρ g x))

/-- Transport the original exact sequence through a linear representation equivalence. -/
def transport : OrdinaryFiltration σ α β where
  injection := e.toLinearMap.comp E.injection
  projection := E.projection.comp e.symm.toLinearMap
  injective := e.injective.comp E.injective
  surjective := E.surjective.comp e.symm.surjective
  exact := by
    ext w
    change E.projection (e.symm w) = 0 ↔ ∃ a, e (E.injection a) = w
    have hh : E.projection (e.symm w) = 0 ↔ ∃ a, E.injection a = e.symm w := by
      change e.symm w ∈ LinearMap.ker E.projection ↔ e.symm w ∈ LinearMap.range E.injection
      rw [E.exact]
    rw [hh]
    exact exists_congr (fun a ↦ e.eq_symm_apply)
  injection_equivariant g a := by
    change σ g (e (E.injection a)) = e (E.injection ((α g : k) * a))
    rw [he, E.injection_equivariant]
  projection_equivariant g w := by
    obtain ⟨x, rfl⟩ := e.surjective w
    change E.projection (e.symm (σ g (e x))) = (β g : k) * E.projection (e.symm (e x))
    rw [he, e.symm_apply_apply, e.symm_apply_apply, E.projection_equivariant]

variable [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace V] [DiscreteTopology V] [TopologicalSpace W] [DiscreteTopology W]
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))
  (hσ : ∀ x : W, Continuous (fun g : G ↦ σ g x))

/-- Transport preserves the actual cocycle obtained from a vector above one. -/
theorem cocycleOf_transport (w : V) (hw : E.projection w = 1) :
    (E.transport e he).cocycleOf hσ (e w) (by simpa [transport] using hw) =
      E.cocycleOf hρ w hw := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  apply LinearMap.ext_ring
  apply (E.transport e he).injective
  change _ = e (E.injection ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).1 g) 1))
  rw [(E.transport e he).cocycleOf_spec hσ (e w) (by simpa [transport] using hw),
    E.cocycleOf_spec hρ w hw, he, map_sub, map_smul]

/-- Transport preserves the extracted extension class in the unchanged Hom coefficients. -/
theorem extensionClass_transport :
    (E.transport e he).extensionClass hσ = E.extensionClass hρ := by
  obtain ⟨w, hw⟩ := E.surjective 1
  rw [(E.transport e he).extensionClass_eq hσ (e w) (by simpa [transport] using hw),
    E.extensionClass_eq hρ w hw, E.cocycleOf_transport e he hρ hσ w hw]

end GaloisRepresentation.Extensions.OrdinaryFiltration
