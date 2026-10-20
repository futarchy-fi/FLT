/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleRingTower

/-!
# Recovering a compatible tower from a stable order

If transitions to a fixed order are bijective thereafter, evaluation at that
order is bijective. Earlier values are obtained by restriction, and later
values by the unique inverse. No inverse-limit exactness is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.CompatibleRingTower
variable {R : ℕ → Type*} [∀ k, CommRing (R k)]
  (ρ : ∀ k l, k ≤ l → R l →+* R k)
  (hcomp : ∀ k l m (h : k ≤ l) (h' : l ≤ m) z,
    ρ k l h (ρ l m h' z) = ρ k m (h.trans h') z)
  (K : ℕ) (hbij : ∀ l (h : K ≤ l), Function.Bijective (ρ K l h))

include hbij in
/-- Agreement at a stable order determines every coefficient of a compatible tower. -/
theorem stable_eval_injective : Function.Injective (eval ρ K) := by
  intro v w h
  change v.val K = w.val K at h
  apply Subtype.ext
  funext k
  by_cases hk : K ≤ k
  · apply (hbij k hk).1
    exact (v.property K k hk).trans (h.trans (w.property K k hk).symm)
  · have hk' : k ≤ K := Nat.le_of_not_ge hk
    rw [← v.property k K hk', ← w.property k K hk', h]

/-- The unique inverse coefficient at an order beyond the stable one. -/
def stableValue (z : R K) (l : ℕ) (h : K ≤ l) : R l :=
  (hbij l h).2 z |>.choose

/-- A chosen stable inverse restricts to its prescribed coefficient. -/
theorem stableValue_spec (z : R K) (l : ℕ) (h : K ≤ l) :
    ρ K l h (stableValue ρ K hbij z l h) = z :=
  (hbij l h).2 z |>.choose_spec

include hcomp in
/-- Unique stable inverses commute with every transition in the tail. -/
theorem stableValue_compatible (z : R K) {k l : ℕ} (hk : K ≤ k) (h : k ≤ l) :
    ρ k l h (stableValue ρ K hbij z l (hk.trans h)) =
      stableValue ρ K hbij z k hk := by
  apply (hbij k hk).1
  rw [hcomp, stableValue_spec, stableValue_spec]

/-- Extend the uniquely determined tail to the earlier orders by actual restriction. -/
def stableLift (z : R K) : ring ρ := by
  let v (k : ℕ) := ρ k (max K k) (le_max_right K k)
    (stableValue ρ K hbij z (max K k) (le_max_left K k))
  refine ⟨v, fun k l h ↦ ?_⟩
  have hm : max K k ≤ max K l := max_le_max_left K h
  have hc := stableValue_compatible ρ hcomp K hbij z (le_max_left K k) hm
  dsimp [v]
  rw [hcomp, ← hc, hcomp]

include hcomp hbij in
/-- Evaluation at the stable order has an explicitly constructed inverse. -/
theorem stable_eval_surjective : Function.Surjective (eval ρ K) := by
  intro z
  refine ⟨stableLift ρ hcomp K hbij z, ?_⟩
  change ρ K (max K K) _ (stableValue ρ K hbij z (max K K) _) = z
  exact stableValue_spec ρ K hbij z _ _

include hcomp hbij in
/-- A stable tail identifies the full compatible ring with one actual stage. -/
theorem stable_eval_bijective : Function.Bijective (eval ρ K) :=
  ⟨stable_eval_injective ρ K hbij, stable_eval_surjective ρ hcomp K hbij⟩

end FLT.Mazur.CompatibleRingTower
