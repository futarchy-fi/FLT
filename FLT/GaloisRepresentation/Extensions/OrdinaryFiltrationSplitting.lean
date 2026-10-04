/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationTwist

/-!
# Detecting splitting in an actual ordinary representation

The split branch means an equivariant linear section of the actual quotient.
It is equivalent to an eigenvector above one and to a vanishing normalized
cocycle for some section. Simultaneous character twists preserve splitting.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions.OrdinaryFiltration

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)

/-- Splitting of the actual equivariant quotient map. -/
def Splits : Prop := ∃ s : k →ₗ[k] V, E.projection.comp s = LinearMap.id ∧
  ∀ g x, ρ g (s x) = s ((β g : k) * x)

/-- An equivariant section is determined by its eigenvector above one. -/
theorem splits_iff_eigenlift : E.Splits ↔
    ∃ w : V, E.projection w = 1 ∧ ∀ g, ρ g w = (β g : k) • w := by
  constructor
  · rintro ⟨s, hs, he⟩
    refine ⟨s 1, LinearMap.congr_fun hs 1, fun g ↦ ?_⟩
    simpa only [← smul_eq_mul, s.map_smul] using he g 1
  · rintro ⟨w, hw, he⟩
    refine ⟨LinearMap.toSpanSingleton k V w, ?_, ?_⟩
    · apply LinearMap.ext
      intro x
      change E.projection (x • w) = x
      simp [hw]
    · intro g x
      change ρ g (x • w) = ((β g : k) * x) • w
      rw [map_smul, he, smul_smul, mul_comm]

/-- Twisting both characters and the middle representation preserves splitting. -/
theorem splits_twist_iff (ψ : G →* kˣ) : (E.twist ψ).Splits ↔ E.Splits := by
  rw [splits_iff_eigenlift, splits_iff_eigenlift]
  constructor
  · rintro ⟨w, hw, he⟩
    refine ⟨w, hw, fun g ↦ ?_⟩
    have h := he g
    change (ψ g : k) • ρ g w = ((β g : k) * (ψ g : k)) • w at h
    apply (smul_right_injective V (ψ g).ne_zero)
    simpa only [smul_smul, mul_comm (ψ g : k)] using h
  · rintro ⟨w, hw, he⟩
    refine ⟨w, hw, fun g ↦ ?_⟩
    change (ψ g : k) • ρ g w = ((β g : k) * (ψ g : k)) • w
    rw [he, smul_smul, mul_comm]

variable [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace V] [DiscreteTopology V]
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))

/-- Vanishing of the extracted cocycle is exactly equivariance of its section. -/
theorem cocycleOf_zero_iff (w : V) (hw : E.projection w = 1) :
    (∀ g, (E.cocycleOf hρ w hw).1 g = 0) ↔ ∀ g, ρ g w = (β g : k) • w := by
  constructor
  · intro hz g
    have h := E.cocycleOf_spec hρ w hw g
    rw [hz g] at h
    change E.injection 0 = (β g : k)⁻¹ • ρ g w - w at h
    rw [map_zero] at h
    have h' := sub_eq_zero.mp h.symm
    have h'' := congrArg (fun x : V ↦ (β g : k) • x) h'
    simpa only [smul_smul, mul_inv_cancel₀ (β g).ne_zero, one_smul] using h''
  · intro he g
    apply LinearMap.ext_ring
    apply E.injective
    rw [E.cocycleOf_spec hρ]
    change (β g : k)⁻¹ • ρ g w - w = E.injection 0
    rw [he, smul_smul, inv_mul_cancel₀ (β g).ne_zero, one_smul, sub_self, map_zero]

/-- The split branch is extracted from the actual normalized difference cocycle. -/
theorem splits_iff_exists_zero_cocycle : E.Splits ↔
    ∃ (w : V) (hw : E.projection w = 1), ∀ g, (E.cocycleOf hρ w hw).1 g = 0 := by
  rw [splits_iff_eigenlift]
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨w, hw, (E.cocycleOf_zero_iff hρ w hw).mpr he⟩
  · rintro ⟨w, hw, hz⟩
    exact ⟨w, hw, (E.cocycleOf_zero_iff hρ w hw).mp hz⟩

end GaloisRepresentation.Extensions.OrdinaryFiltration
