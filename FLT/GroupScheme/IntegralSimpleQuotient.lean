/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.IntegralSimpleSubobject

/-!
# Simple integral quotients

A maximal proper stable subgroup of geometric points produces a simple
integral quotient. The kernel has strictly smaller order, so recursion gives
filtrations in the same direction as `HasFiltration`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [IsDedekindDomain R] [IsPrincipalIdealRing R]

/-- Every nonzero finite-flat object has a simple integral quotient with smaller kernel. -/
theorem FiniteFlatObject.existsSimpleQuotient (H : FiniteFlatObject R) [Nontrivial H.points] :
    ∃ A Q : FiniteFlatObject R, ∃ _ : FiniteFlatExtension A H Q,
      Simple Q ∧ Nat.card A.points < Nat.card H.points := by
  classical
  obtain ⟨P, hP⟩ := exists_maximal_of_wellFoundedGT
    (fun P : AddSubgroup H.points ↦ P ≠ ⊤ ∧ GaloisStable H.points P)
    ⟨⊥, bot_ne_top, fun σ x hx ↦ by
      rw [AddSubgroup.mem_bot] at hx ⊢
      rw [hx, smul_zero]⟩
  obtain ⟨A, Q, E, hE⟩ := H.existsExtensionOfGaloisStable P hP.prop.2
  let q := (FiniteFlatObject.pointMap E.quotient).toAddMonoidHom
  have hker : q.ker = P := E.pointKernelEqRange.trans hE
  have hQ : Nontrivial Q.points := by
    by_contra hn
    have hsub : Subsingleton Q.points := not_nontrivial_iff_subsingleton.mp hn
    apply hP.prop.1
    apply top_unique
    intro x _
    rw [← hker]
    exact hsub.elim _ _
  have hs : Simple Q := by
    refine ⟨hQ, ?_⟩
    intro B hB
    by_cases htop : B = ⊤
    · exact Or.inr htop
    left
    have hcomap : GaloisStable H.points (B.comap q) := by
      intro σ x hx
      change FiniteFlatObject.pointMap E.quotient (σ • x) ∈ B
      rw [map_smul]
      exact hB σ (q x) hx
    have hcomaptop : B.comap q ≠ ⊤ := by
      intro ht
      apply htop
      apply top_unique
      intro y _
      obtain ⟨x, rfl⟩ := E.pointsSurjective y
      exact show x ∈ B.comap q from ht ▸ AddSubgroup.mem_top x
    have hle : P ≤ B.comap q := by
      intro x hx
      rw [← hker] at hx
      change q x ∈ B
      rw [show q x = 0 from hx]
      exact B.zero_mem
    have hback : B.comap q ≤ P := hP.le_of_ge ⟨hcomaptop, hcomap⟩ hle
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := E.pointsSurjective y
      have hx := hback hy
      rw [← hker] at hx
      exact hx
    · exact bot_le
  refine ⟨A, Q, E, hs, ?_⟩
  rw [← E.cardPoints]
  have hA : 0 < Nat.card A.points := Nat.card_pos
  have hQcard : 1 < Nat.card Q.points := @Finite.one_lt_card Q.points _ hQ
  nlinarith

end ThreeAdicPlan
