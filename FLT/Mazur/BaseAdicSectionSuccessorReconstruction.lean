/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicSectionReconstruction

/-!
# Reconstructing sections from positive adic powers

Original infinitesimal stages start at the first ideal power. Their compatible
sections suffice for reconstruction; the zeroth quotient adds no data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Scheme.Modules
open FLT.Mazur.BaseAdicThickening FLT.Mazur.IdealAdicQuotient

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  [IsAdicComplete J R] (M : X.Modules) [M.IsFinitePresentation]

/-- Compatible sections at all positive ideal powers determine one actual global section. -/
theorem existsUnique_globalSection_succ :
    let _ := Chow.source_isNoetherian f
    ∀ s : ∀ n, Γ(quotient ((baseIdeal R J).comap f) M (n + 1), ⊤),
      (∀ a b (hab : a ≤ b),
        (reduction ((baseIdeal R J).comap f) M (Nat.add_le_add_right hab 1)).app ⊤
          (s b) = s a) →
      ∃! t : Γ(M, ⊤),
        ∀ n, (projection ((baseIdeal R J).comap f) M (n + 1)).app ⊤ t = s n := by
  let _ := Chow.source_isNoetherian f
  dsimp only
  intro s hs
  let I := (baseIdeal R J).comap f
  let s' : ∀ n, Γ(quotient I M n, ⊤)
    | 0 => (reduction I M (Nat.zero_le 1)).app ⊤ (s 0)
    | n + 1 => s n
  have hs' (a b : ℕ) (hab : a ≤ b) : (reduction I M hab).app ⊤ (s' b) = s' a := by
    cases a with
    | zero =>
      cases b with
      | zero => simp only [reduction_refl, Hom.id_app, ConcreteCategory.id_apply]
      | succ b =>
        change (reduction I M (Nat.zero_le (b + 1))).app ⊤ (s b) = _
        rw [← reduction_trans I M (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le b))]
        change (reduction I M (Nat.zero_le 1)).app ⊤
          ((reduction I M (Nat.succ_le_succ (Nat.zero_le b))).app ⊤ (s b)) = _
        rw [hs 0 b (Nat.zero_le b)]
    | succ a =>
      cases b with
      | zero => exact (Nat.not_succ_le_zero a hab).elim
      | succ b => exact hs a b (Nat.le_of_succ_le_succ hab)
  obtain ⟨t, ht, hu⟩ := existsUnique_globalSection f J M s' hs'
  refine ⟨t, fun n ↦ ht (n + 1), ?_⟩
  intro y hy
  apply hu
  intro n
  cases n with
  | zero =>
    change (projection I M 0).app ⊤ y = _
    rw [← projection_reduction I M (Nat.zero_le 1)]
    change (reduction I M (Nat.zero_le 1)).app ⊤ ((projection I M 1).app ⊤ y) = _
    rw [hy 0]
  | succ n => exact hy n

end FLT.Mazur.BaseAdicCohomology
