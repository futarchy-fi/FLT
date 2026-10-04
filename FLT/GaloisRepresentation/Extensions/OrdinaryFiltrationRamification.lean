/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationSplitting
public import FLT.LocalClassFieldTheory.PeuClassSubmodule

/-!
# Independent ramification of actual ordinary filtrations

The cup-annihilator condition is applied to the extracted class. Splitting
implies this condition, so a non-peu class forces a nonsplit representation.
The predicate is invariant under line basis changes and simultaneous twists.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions

open LocalClassFieldTheory

variable {G k M N : Type*} [Group G] [TopologicalSpace G]
  [Field k] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup N] [Module k N] [DistribMulAction G N] [SMulCommClass G k N]
  [TopologicalSpace N] [DiscreteTopology N]

/-- Linear coefficient transport preserves the independent predicate on explicit classes. -/
theorem isPeuRamifiedClass_mapCoefficient_iff (I : Subgroup G) (e : M ≃ₗ[k] N)
    (he : ∀ (g : G) (x : M), e (g • x) = g • e x) (x : ContinuousClass G M) :
    IsPeuRamifiedClass (k := k) I (mapCoefficientClass e.toAddEquiv he x) ↔
      IsPeuRamifiedClass (k := k) I x := by
  induction x using Quotient.inductionOn with | h c =>
    exact isPeuRamified_linearEquiv_iff I e he (linearCocycleOf c)

namespace OrdinaryFiltration

variable {V : Type*} [AddCommGroup V] [Module k V]
  [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x)) (I : Subgroup G)

/-- The independent condition on the class extracted from the actual middle representation. -/
def IsPeu : Prop := IsPeuRamifiedClass (k := k) I (E.extensionClass hρ)

/-- An actual equivariant splitting has zero cup against every unramified test character. -/
theorem isPeu_of_splits (hs : E.Splits) : E.IsPeu hρ I := by
  obtain ⟨w, hw, hz⟩ := (E.splits_iff_exists_zero_cocycle hρ).mp hs
  unfold IsPeu
  rw [E.extensionClass_eq hρ w hw]
  intro d _
  refine ⟨0, fun g h ↦ ?_⟩
  change g • (0 : OrdinaryHomModule α β) - 0 + 0 = d.1 h • (E.cocycleOf hρ w hw).1 g
  rw [hz]
  simp

/-- Non-peu ramification excludes the split branch without any finite-flat premise. -/
theorem not_splits_of_not_isPeu (hn : ¬ E.IsPeu hρ I) : ¬ E.Splits :=
  fun hs ↦ hn (E.isPeu_of_splits hρ I hs)

/-- Rescaling either actual line coordinate preserves and reflects ramification. -/
theorem isPeu_change_bases (D : OrdinaryFiltration ρ α β) (a b : kˣ)
    (hi : D.injection = (a : k) • E.injection)
    (hp : D.projection = (b : k)⁻¹ • E.projection) :
    D.IsPeu hρ I ↔ E.IsPeu hρ I := by
  unfold IsPeu
  rw [E.extensionClass_change_bases D hρ a b hi hp]
  exact isPeuRamifiedClass_mapCoefficient_iff I (LinearEquiv.smulOfUnit (b / a))
    (scalarCoefficientEquiv_equivariant (b / a)) _

/-- Simultaneous twists preserve and reflect ramification of the actual extension. -/
theorem isPeu_twist (ψ : G →* kˣ) (hψ : Continuous (fun g : G ↦ (ψ g : k))) :
    (E.twist ψ).IsPeu (continuous_twistOrbit ψ hρ hψ) I ↔ E.IsPeu hρ I := by
  unfold IsPeu
  rw [E.extensionClass_twist ψ hρ hψ]
  exact isPeuRamifiedClass_mapCoefficient_iff I
    ({ ordinaryHomTwistEquiv α β ψ with map_smul' := fun _ _ ↦ rfl } :
      OrdinaryHomModule α β ≃ₗ[k] OrdinaryHomModule (α * ψ) (β * ψ))
    (ordinaryHomTwistEquiv_equivariant α β ψ) _

end OrdinaryFiltration
end GaloisRepresentation.Extensions
