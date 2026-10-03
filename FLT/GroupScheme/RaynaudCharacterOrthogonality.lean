/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterProjector

/-!
# Orthogonality of character projectors

Translation of a finite character sum proves its vanishing. Applied to the
ratio of two characters, this shows that a projector kills every other
character eigenspace, without a rank or freeness hypothesis on that space.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
namespace CharacterProjector

variable {R G V : Type*} [CommRing R] [IsDomain R] [Group G] [Fintype G]
  [AddCommGroup V] [Module R V]

/-- A nontrivial unit-valued character has vanishing sum. -/
theorem sum_character_eq_zero (χ : G →* Rˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : R) = 0 := by
  obtain ⟨g, hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra! h
    exact hχ (MonoidHom.ext h)
  refine eq_zero_of_mul_eq_self_left (show (χ g : R) ≠ 1 by simpa using hg) ?_
  simpa only [Finset.mul_sum, ← Units.val_mul, ← map_mul] using
    (Group.mulLeft_bijective g).sum_comp (fun h ↦ (χ h : R))

variable [Invertible (Fintype.card G : R)] (ρ : Representation R G V)

omit [IsDomain R] in
/-- Projecting an eigenvector reduces to the sum of the ratio character. -/
theorem projector_on_eigenvector (χ ψ : G →* Rˣ) (v : V)
    (hv : v ∈ eigenspace ρ ψ) :
    projector ρ χ v = (⅟(Fintype.card G : R) *
      ∑ g : G, ((χ⁻¹ * ψ) g : R)) • v := by
  rw [projector_apply]
  simp_rw [(mem_eigenspace_iff ρ ψ v).mp hv, smul_smul]
  rw [← Finset.sum_smul, smul_smul]
  rfl

/-- Distinct character projectors annihilate each other's eigenspaces. -/
theorem projector_eq_zero_of_ne (χ ψ : G →* Rˣ) (h : χ ≠ ψ)
    (v : V) (hv : v ∈ eigenspace ρ ψ) : projector ρ χ v = 0 := by
  rw [projector_on_eigenvector ρ χ ψ v hv, sum_character_eq_zero]
  · simp
  · exact fun h' ↦ h (inv_mul_eq_one.mp h')

/-- The derived projectors are pairwise orthogonal endomorphisms. -/
theorem projector_comp_eq_zero (χ ψ : G →* Rˣ) (h : χ ≠ ψ) :
    (projector ρ χ).comp (projector ρ ψ) = 0 := by
  ext v
  exact projector_eq_zero_of_ne ρ χ ψ h _ (projector_mem ρ ψ v)

/-- Distinct character eigenspaces have zero intersection. -/
theorem disjoint_eigenspace (χ ψ : G →* Rˣ) (h : χ ≠ ψ) :
    Disjoint (eigenspace ρ χ) (eigenspace ρ ψ) := by
  rw [Submodule.disjoint_def]
  intro v hv hψ
  rw [← projector_eq_self ρ χ v hv, projector_eq_zero_of_ne ρ χ ψ h v hψ]

end CharacterProjector
end ThreeAdicPlan
