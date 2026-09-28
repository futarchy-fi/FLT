/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import Mathlib.GroupTheory.PGroup

/-!
# Simple objects of category D are killed by three

The three-torsion subgroup is Galois-stable. Cauchy's theorem makes it
nonzero in a nonzero three-primary object, so simplicity makes it the
entire point group.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- The kernel of multiplication by an integer is stable under the Galois action. -/
theorem galoisStable_nsmul_ker (W : FiniteContinuousGaloisModule) (n : ℕ) :
    GaloisStable W (nsmulAddMonoidHom (α := W) n).ker := by
  intro σ w hw
  change n • w = 0 at hw
  change n • (σ • w) = 0
  let f : W →+ W :=
    { toFun := fun x ↦ σ • x
      map_zero' := smul_zero σ
      map_add' := smul_add σ }
  simpa only [map_nsmul, map_zero, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
    congrArg f hw

/-- A simple object of category D is annihilated by three. -/
theorem simple_D_killed_three (H : FF ZInvTwo) (hs : Simple H) (hD : InCategoryD H) :
    KilledBy 3 H := by
  let : Nontrivial H.points := hs.1
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hD.threePrimary
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn
    let : Subsingleton H.points := (Nat.card_eq_one_iff_unique.mp hn).1
    exact false_of_nontrivial_of_subsingleton H.points
  have hdvd : 3 ∣ Nat.card H.points := by
    rw [hn]
    exact dvd_pow_self 3 hn0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := H.points) 3 hdvd
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hx3 : (3 : ℕ) • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  rcases hs.2 _ (galoisStable_nsmul_ker H.points 3) with hker | hker
  · have hxmem : x ∈ (nsmulAddMonoidHom (α := H.points) 3).ker := hx3
    rw [hker, AddSubgroup.mem_bot] at hxmem
    exact (hx0 hxmem).elim
  · intro w
    have hw : w ∈ (nsmulAddMonoidHom (α := H.points) 3).ker := by rw [hker]; trivial
    exact hw

end ThreeAdicPlan
