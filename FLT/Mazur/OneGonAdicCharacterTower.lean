/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterStep

/-!
# Constructing the compatible original character-group tower

Recursion through the proved square-zero step extends the specified original
homomorphism. Every stage is an actual group-scheme homomorphism, and the full
adjacent reduction squares and uniqueness follow from the construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The recursively constructed original character-group homomorphisms. -/
def tower : (m : ℕ) → stageSource I G m ⟶ stageGroup I t m
  | 0 => g
  | m + 1 => step I t ht m (tower m)

/-- The initial stage is exactly the specified original homomorphism. -/
theorem tower_zero : tower I t ht g 0 = g := rfl

/-- Each stage retains the full previous original morphism under the genuine reduction. -/
theorem tower_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
      (tower I t ht g (m + 1)).hom.hom.hom.left =
        (tower I t ht g m).hom.hom.hom.left ≫ smoothRestriction I t m :=
  step_reduction I t ht m (tower I t ht g m)

/-- Any tower retaining the same original map and all adjacent reductions is this tower. -/
theorem tower_unique (q : (m : ℕ) → stageSource I G m ⟶ stageGroup I t m)
    (h0 : q 0 = g)
    (hq : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
      (q (m + 1)).hom.hom.hom.left =
        (q m).hom.hom.hom.left ≫ smoothRestriction I t m) :
    q = tower I t ht g := by
  funext m
  induction m with
  | zero => exact h0
  | succ m ih =>
    apply step_unique I t ht m (tower I t ht g m)
    rw [hq m, ih]

end FLT.Mazur.OneGonAdicCharacterTower
