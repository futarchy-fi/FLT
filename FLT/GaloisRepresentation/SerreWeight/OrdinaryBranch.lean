/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationRamification
public import FLT.GaloisRepresentation.SerreWeight.NormalizedRecipe

/-!
# Extracting the ordinary branch from the representation

Splitting means an actual equivariant section. The exceptional branch tests
the whole-group Hom character and the independent cup-annihilator class.
No branch label or asserted weight is supplied with the representation.
The parameter `ε` must be instantiated with the local cyclotomic character;
this file does not identify arbitrary inertia types or evaluate Serre weights.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.Extensions.OrdinaryFiltration
open SerreWeightRecipe

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))
  (I : Subgroup G) (ε : G →* kˣ)

/-- Branch selection from splitting, the actual Hom character, and the extracted class. -/
def ordinaryBranch : ExtensionCase := by
  classical
  exact if E.Splits then .split
  else if homCharacter α β = ε ∧ ¬ E.IsPeu hρ I then .cyclotomicTres
  else .nonsplit

/-- The selected split branch is exactly actual equivariant splitting. -/
theorem ordinaryBranch_split_iff : E.ordinaryBranch hρ I ε = .split ↔ E.Splits := by
  classical
  simp only [ordinaryBranch]
  split <;> simp_all
  split <;> simp_all

/-- The exceptional branch is detected by the independent non-peu condition. -/
theorem ordinaryBranch_tres_iff : E.ordinaryBranch hρ I ε = .cyclotomicTres ↔
    homCharacter α β = ε ∧ ¬ E.IsPeu hρ I := by
  classical
  by_cases hs : E.Splits
  · have hp := E.isPeu_of_splits hρ I hs
    simp [ordinaryBranch, hs, hp]
  · simp [ordinaryBranch, hs]

/-- The residual branch is nonsplit and fails the exceptional whole-local test. -/
theorem ordinaryBranch_nonsplit_iff : E.ordinaryBranch hρ I ε = .nonsplit ↔
    ¬ E.Splits ∧ (homCharacter α β ≠ ε ∨ E.IsPeu hρ I) := by
  classical
  by_cases hs : E.Splits <;> by_cases he : homCharacter α β = ε <;>
    by_cases hp : E.IsPeu hρ I <;> simp [ordinaryBranch, hs, he, hp]

/-- Twisting the actual middle representation and both lines preserves the branch. -/
theorem ordinaryBranch_twist (ψ : G →* kˣ)
    (hψ : Continuous (fun g : G ↦ (ψ g : k))) :
    (E.twist ψ).ordinaryBranch (continuous_twistOrbit ψ hρ hψ) I ε =
      E.ordinaryBranch hρ I ε := by
  classical
  unfold ordinaryBranch
  rw [E.splits_twist_iff, homCharacter_twist, E.isPeu_twist hρ I ψ hψ]

omit [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace V] [DiscreteTopology V] in
/-- Rescaling the quotient coordinate preserves equivariant splitting. -/
theorem splits_change_quotient_basis (D : OrdinaryFiltration ρ α β) (b : kˣ)
    (hp : D.projection = (b : k)⁻¹ • E.projection) : D.Splits ↔ E.Splits := by
  rw [splits_iff_eigenlift, splits_iff_eigenlift]
  constructor
  · rintro ⟨w, hw, he⟩
    refine ⟨(b : k)⁻¹ • w, ?_, fun g ↦ ?_⟩
    · simpa only [hp, LinearMap.smul_apply, map_smul] using hw
    · rw [map_smul, he, smul_comm]
  · rintro ⟨w, hw, he⟩
    refine ⟨(b : k) • w, ?_, fun g ↦ ?_⟩
    · simp [hp, hw]
    · rw [map_smul, he, smul_comm]

/-- The branch is independent of both chosen line bases. -/
theorem ordinaryBranch_change_bases (D : OrdinaryFiltration ρ α β) (a b : kˣ)
    (hi : D.injection = (a : k) • E.injection)
    (hp : D.projection = (b : k)⁻¹ • E.projection) :
    D.ordinaryBranch hρ I ε = E.ordinaryBranch hρ I ε := by
  classical
  unfold ordinaryBranch
  rw [E.splits_change_quotient_basis D b hp, E.isPeu_change_bases hρ I D a b hi hp]

end GaloisRepresentation.Extensions.OrdinaryFiltration
