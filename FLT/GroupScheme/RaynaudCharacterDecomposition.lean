/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterOrthogonality
public import FLT.GroupScheme.RaynaudHenselianCharacters

/-!
# The character decomposition

Dual character orthogonality proves that the sum of the averaging projectors
is the identity. The resulting equivalence decomposes the actual module into
its derived character eigenspaces.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
namespace CharacterProjector

variable {R G V : Type*} [CommRing R] [IsDomain R] [CommGroup G] [Fintype G]
  [AddCommGroup V] [Module R V] [HasEnoughRootsOfUnity R (Monoid.exponent G)]
  [Fintype (G →* Rˣ)] [Invertible (Fintype.card G : R)]

omit [Invertible (Fintype.card G : R)] in
/-- Summing the inverse characters at a group element gives the delta function. -/
theorem sum_inverse_characters [DecidableEq G] (g : G) :
    ∑ χ : G →* Rˣ, (↑(χ g)⁻¹ : R) = if g = 1 then (Fintype.card G : R) else 0 := by
  classical
  by_cases hg : g = 1
  · subst g
    have hc := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G R
    simp only [Nat.card_eq_fintype_card] at hc
    simp [hc]
  · simp only [hg, ↓reduceIte]
    let ev : (G →* Rˣ) →* Rˣ :=
      { toFun := fun χ ↦ (χ g)⁻¹
        map_one' := by simp
        map_mul' := by intros; simp [mul_comm] }
    apply sum_character_eq_zero ev
    obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G R hg
    intro he
    have h := DFunLike.congr_fun he χ
    exact hχ (by simpa [ev] using h)

/-- The sum of all character projectors recovers every vector. -/
theorem sum_projector (ρ : Representation R G V) (v : V) :
    ∑ χ : G →* Rˣ, projector ρ χ v = v := by
  classical
  simp_rw [projector_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_inverse_characters]
  simp [ite_smul]

/-- The complete decomposition into eigenspaces defined from the representation. -/
def decomposition (ρ : Representation R G V) : V ≃ₗ[R] ((χ : G →* Rˣ) → eigenspace ρ χ) where
  toFun v χ := ⟨projector ρ χ v, projector_mem ρ χ v⟩
  invFun v := ∑ χ, (v χ : V)
  left_inv := sum_projector ρ
  right_inv v := by
    classical
    funext χ
    apply Subtype.ext
    change projector ρ χ (∑ ψ, (v ψ : V)) = v χ
    rw [map_sum, Finset.sum_eq_single χ]
    · exact projector_eq_self ρ χ _ (v χ).property
    · intro ψ _ hψ
      exact projector_eq_zero_of_ne ρ χ ψ (Ne.symm hψ) _ (v ψ).property
    · simp
  map_add' v w := by ext χ; exact map_add (projector ρ χ) v w
  map_smul' r v := by ext χ; exact map_smul (projector ρ χ) r v

/-- The decomposition component is exactly the corresponding character projector. -/
@[simp] theorem decomposition_apply (ρ : Representation R G V) (v : V) (χ : G →* Rˣ) :
    (decomposition ρ v χ : V) = projector ρ χ v := rfl

end CharacterProjector
end ThreeAdicPlan
