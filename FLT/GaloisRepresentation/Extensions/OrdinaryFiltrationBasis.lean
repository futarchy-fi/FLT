/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationClass
public import FLT.GaloisRepresentation.Extensions.CharacterBasis

/-!
# Changing the two bases of an actual ordinary filtration

Rescaling the sub-line by a and quotient-line by b transports the extracted
class by b/a. Both classes are constructed from the middle representation.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.Extensions.OrdinaryFiltration

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
    [TopologicalSpace V] [DiscreteTopology V]
    {ρ : Representation k G V} {α β : G →* kˣ}
    (E D : OrdinaryFiltration ρ α β)
    (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))

/-- The extracted cocycle satisfies the normalized difference equation in the middle space. -/
theorem cocycleOf_spec (w : V) (hw : E.projection w = 1) (g : G) :
    E.injection ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).1 g) 1) =
      (β g : k)⁻¹ • ρ g w - w := by
  have h := congrArg (fun f : OrdinarySectionModule ρ β ↦ (show k →ₗ[k] V from f) 1)
    (liftCocycle_spec E.homInjection (E.sectionOf w) (E.section_difference_range w hw) g)
  change E.injection _ = ρ g ((((β g⁻¹ : kˣ) : k) * 1) • w) - (1 : k) • w at h
  simpa only [cocycleOf, ContinuousMap.coe_mk, mul_one, one_smul, map_inv,
    Units.val_inv_eq_inv_val, map_smul] using h

/-- Rescaling the two actual line coordinates transports the constructed cocycle. -/
theorem cocycleOf_change_bases (a b : kˣ)
    (hi : D.injection = (a : k) • E.injection)
    (w : V) (hw : E.projection w = 1)
    (hz : D.projection ((b : k) • w) = 1) :
    D.cocycleOf hρ ((b : k) • w) hz =
      mapCoefficientCocycle (scalarCoefficientEquiv (b / a))
        (scalarCoefficientEquiv_equivariant (b / a)) (E.cocycleOf hρ w hw) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  apply LinearMap.ext_ring
  apply D.injective
  rw [D.cocycleOf_spec hρ]
  change _ = D.injection (((b / a : kˣ) : k) *
    ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).1 g) 1))
  rw [hi, LinearMap.smul_apply, ← smul_eq_mul]
  simp only [map_smul, smul_smul, Units.val_div_eq_div_val]
  rw [mul_div_cancel₀ _ a.ne_zero, E.cocycleOf_spec hρ, smul_sub, smul_smul,
    mul_comm (↑(β g))⁻¹ (b : k)]

/-- Basis changes transport the section-independent extension class by b/a. -/
theorem extensionClass_change_bases (a b : kˣ)
    (hi : D.injection = (a : k) • E.injection)
    (hp : D.projection = (b : k)⁻¹ • E.projection) :
    D.extensionClass hρ = mapCoefficientClass (scalarCoefficientEquiv (b / a))
      (scalarCoefficientEquiv_equivariant (b / a)) (E.extensionClass hρ) := by
  obtain ⟨w, hw⟩ := E.surjective 1
  have hz : D.projection ((b : k) • w) = 1 := by
    rw [hp, LinearMap.smul_apply, map_smul, hw, smul_smul, inv_mul_cancel₀ b.ne_zero,
      one_smul]
  rw [D.extensionClass_eq hρ _ hz, E.extensionClass_eq hρ w hw,
    E.cocycleOf_change_bases D hρ a b hi w hw hz]
  rfl

end GaloisRepresentation.Extensions.OrdinaryFiltration
