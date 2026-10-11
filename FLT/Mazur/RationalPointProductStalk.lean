/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RationalPointDivisorStalk

/-!
# Stalks of finite products of rational point powers

Distinct rational point images separate the factors. At one of the points only
its own factor remains; away from all the points the full product is the unit ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsSeparated f]
  {ι : Type*} [Fintype ι] (p : ι → (Spec (.of k) ⟶ X))
  (hp : ∀ i, p i ≫ f = 𝟙 _) (n : ι → ℕ)

include hp in
/-- At a distinct point image, only its own ideal-power factor survives. -/
theorem rationalPointProduct_stalk
    (hinj : Function.Injective (fun i ↦ p i (IsLocalRing.closedPoint k))) (i : ι) :
    stalkIdeal (∏ j, (p j).ker ^ n j) (p i (IsLocalRing.closedPoint k)) =
      stalkIdeal (p i).ker (p i (IsLocalRing.closedPoint k)) ^ n i := by
  classical
  rw [stalkIdeal_prod]
  simp only [stalkIdeal_pow]
  apply Finset.prod_eq_single i
  · intro j _ hji
    rw [rationalPointIdeal_stalk_of_ne f (p j) (hp j) _
      (fun h ↦ hji (hinj h).symm), one_pow]
  · simp

include hp in
/-- Away from every point image the full finite product has unit stalk. -/
theorem rationalPointProduct_stalk_of_notMem (x : X)
    (hx : ∀ i, x ≠ p i (IsLocalRing.closedPoint k)) :
    stalkIdeal (∏ i, (p i).ker ^ n i) x = 1 := by
  rw [stalkIdeal_prod]
  apply Finset.prod_eq_one
  intro i _
  rw [stalkIdeal_pow, rationalPointIdeal_stalk_of_ne f (p i) (hp i) x (hx i), one_pow]

end FLT.Mazur.FCurve
