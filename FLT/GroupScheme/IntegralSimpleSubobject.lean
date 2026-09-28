/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CategoryDExactSubquotients
public import Mathlib.Order.Minimal

/-!
# Simple integral subobjects

A minimal nonzero Galois-stable subgroup gives a simple integral kernel in an
extension of the chosen middle model. The quotient is strictly smaller, which
permits recursion without replacing integral exactness by point exactness.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [IsDedekindDomain R] [IsPrincipalIdealRing R]

/-- Every nonzero finite-flat object has a simple integral kernel and a smaller quotient. -/
theorem FiniteFlatObject.existsSimpleKernel (H : FiniteFlatObject R) [Nontrivial H.points] :
    ∃ A Q : FiniteFlatObject R, ∃ _ : FiniteFlatExtension A H Q,
      Simple A ∧ Nat.card Q.points < Nat.card H.points := by
  classical
  obtain ⟨P, hP⟩ := exists_minimal_of_wellFoundedLT
    (fun P : AddSubgroup H.points ↦ P ≠ ⊥ ∧ GaloisStable H.points P)
    ⟨⊤, top_ne_bot, fun _ _ _ ↦ AddSubgroup.mem_top _⟩
  obtain ⟨A, Q, E, hE⟩ := H.existsExtensionOfGaloisStable P hP.prop.2
  let i := (FiniteFlatObject.pointMap E.inclusion).toAddMonoidHom
  have hi : Function.Injective i := E.pointsInjective
  have hA : Nontrivial A.points := by
    by_contra hn
    have hsub : Subsingleton A.points := not_nontrivial_iff_subsingleton.mp hn
    apply hP.prop.1
    rw [← hE]
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      simp [hsub.elim a 0]
    · exact bot_le
  let nontrivialA : Nontrivial A.points := hA
  refine ⟨A, Q, E, ⟨hA, ?_⟩, E.cardRightLt⟩
  intro B hB
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  right
  have hmap : GaloisStable H.points (B.map i) := by
    rintro σ _ ⟨b, hb, rfl⟩
    exact ⟨σ • b, hB σ b hb, map_smul (FiniteFlatObject.pointMap E.inclusion) σ b⟩
  have hmapbot : B.map i ≠ ⊥ := by
    intro hzero
    apply hbot
    apply le_antisymm
    · intro b hb
      have hx : i b ∈ B.map i := ⟨b, hb, rfl⟩
      rw [hzero] at hx
      exact hi (by simpa using hx)
    · exact bot_le
  have hle : B.map i ≤ P := by
    rw [← hE]
    rintro x ⟨b, _, rfl⟩
    exact ⟨b, rfl⟩
  have hback : P ≤ B.map i := hP.le_of_le ⟨hmapbot, hmap⟩ hle
  apply top_unique
  intro a _
  have ha : i a ∈ P := hE ▸ (show i a ∈ i.range from ⟨a, rfl⟩)
  obtain ⟨b, hb, hab⟩ := hback ha
  exact hi hab ▸ hb

end ThreeAdicPlan
