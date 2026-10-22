/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteScalarResidualCorrections
public import FLT.Mazur.RelativeDoubleRankExactDenominators

/-!
# Shared residual corrections on full independent rank charts

The finite off-diagonal family permits different residual corrections on
each chart. An explicit power constructs one correction valid on the whole
rectangle. All equations are in full global sections at the prescribed orders.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
open FiniteScalarResidualCorrections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual off-diagonal indices; diagonal charts impose no collision equation. -/
abbrev doubleRankOffDiagonal (N : ℕ) :=
  {i : Fin (N + 1) × Fin (N + 1) // i.1.val ≠ i.2.val}

variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  (x y : T ⟶ A) {R : Type} [CommRing R] (σ : R →+* Γ(T, ⊤))

/-- The full coefficient map for a single off-diagonal index. -/
def doubleRankOffDiagonalScalar (N r s : ℕ) (i : doubleRankOffDiagonal N) :
    R →+* Γ(doubleRankThickening E x y i.val.1.val i.val.2.val r s, ⊤) :=
  (doubleRankMap E x y i.val.1.val i.val.2.val r s).appTop.hom.comp σ

/-- Reindex the exact collision equations by their finite off-diagonal charts. -/
theorem doubleRankCollisionKernel_eq_offDiagonal (N r s : ℕ) :
    doubleRankCollisionKernel E x y σ N r s =
      ⨅ i : doubleRankOffDiagonal N, RingHom.ker (doubleRankOffDiagonalScalar E x y σ N r s i) := by
  ext a
  rw [mem_doubleRankCollisionKernel, Ideal.mem_iInf]
  exact ⟨fun h i ↦ h i.val.1 i.val.2 i.property,
    fun h n m hnm ↦ h ⟨(n, m), hnm⟩⟩

/-- Adding a residual ideal after intersecting kernels means one scalar works on all charts. -/
theorem mem_doubleRank_kernel_sup_iff (N r s : ℕ) (J : Ideal R) (a : R) :
    a ∈ doubleRankCollisionKernel E x y σ N r s ⊔ J ↔
      ∃ b ∈ J, ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap E x y n.val m.val r s).appTop (σ a) =
          (doubleRankMap E x y n.val m.val r s).appTop (σ b) := by
  rw [doubleRankCollisionKernel_eq_offDiagonal, mem_iInf_kernel_sup_iff]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, fun n m hnm ↦ h ⟨(n, m), hnm⟩⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, fun i ↦ h i.val.1 i.val.2 i.property⟩

/-- The number of off-diagonal charts bounds the cost of combining independent corrections. -/
theorem doubleRank_residual_power_le (N r s : ℕ) (J Q : Ideal R) (k : ℕ)
    (h : ∀ n m : Fin (N + 1), n.val ≠ m.val →
      Q ^ k ≤ doubleRankScalarKernel E x y σ n.val m.val r s ⊔ J) :
    Q ^ (Nat.card (doubleRankOffDiagonal N) * k) ≤
      doubleRankCollisionKernel E x y σ N r s ⊔ J := by
  rw [doubleRankCollisionKernel_eq_offDiagonal]
  exact pow_le_shared_kernel (doubleRankOffDiagonalScalar E x y σ N r s) J Q k
    (fun i ↦ h i.val.1 i.val.2 i.property)

/-- Finitely generated targets need only chartwise radical equations to give a shared power. -/
theorem exists_doubleRank_residual_power (N r s : ℕ) (J Q : Ideal R) (hfg : Q.FG)
    (h : ∀ n m : Fin (N + 1), n.val ≠ m.val →
      Q ≤ (doubleRankScalarKernel E x y σ n.val m.val r s ⊔ J).radical) :
    ∃ k : ℕ, Q ^ k ≤ doubleRankCollisionKernel E x y σ N r s ⊔ J := by
  rw [doubleRankCollisionKernel_eq_offDiagonal]
  exact exists_pow_le_shared_kernel (doubleRankOffDiagonalScalar E x y σ N r s) J Q hfg
    (fun i ↦ h i.val.1 i.val.2 i.property)

end FLT.Mazur.RelativeOrderedTuples
