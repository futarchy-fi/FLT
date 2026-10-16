/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDistinctTupleLift
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Ordered distinct tuples on arbitrary scheme tests

A tuple which stays injectively labeled on every nonempty further test
avoids every original collision scheme. This constructs a distinct-tuple
lift without the one-point hypothesis of the geometric lifting API.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [IsSeparated E.hom]
  (I : Type) [Fintype I] {T : Over S} (a : I → (T ⟶ E))
  (ha : ∀ (U : Over S) (z : U ⟶ T), Nonempty U.left →
    Function.Injective (fun i ↦ z ≫ a i))

include ha in
/-- Universal distinctness excludes the entire scheme-theoretic collision locus. -/
theorem universalLift_range_distinct :
    Set.range (lift E I a).left ⊆ (distinctOpen E I : Set (tuples E I).left) := by
  rintro _ ⟨x, rfl⟩
  apply (mem_distinctOpen E I _).mpr
  intro i j hij hc
  obtain ⟨y, hy⟩ := hc
  let W := pullback (lift E I a) (collisionInclusion E I i j)
  obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback (lift E I a) (collisionInclusion E I i j)).map
      (Over.forget S)) x y hy.symm
  have hw : Nonempty W.left := ⟨w⟩
  apply hij
  apply ha W (pullback.fst (lift E I a) (collisionInclusion E I i j)) hw
  calc
    _ = (pullback.fst (lift E I a) (collisionInclusion E I i j) ≫ lift E I a) ≫
        coordinate E I i := by rw [Category.assoc, lift_coordinate]
    _ = (pullback.snd (lift E I a) (collisionInclusion E I i j) ≫
        collisionInclusion E I i j) ≫ coordinate E I i := by rw [pullback.condition]
    _ = (pullback.snd (lift E I a) (collisionInclusion E I i j) ≫
        collisionInclusion E I i j) ≫ coordinate E I j := by
      rw [Category.assoc, collision_condition, ← Category.assoc]
    _ = _ := by rw [← pullback.condition, Category.assoc, lift_coordinate]

/-- The actual distinct-tuple lift over an arbitrary scheme test. -/
def universalDistinctLift : T ⟶ distinctScheme E I := by
  have hr : Set.range (lift E I a).left ⊆ Set.range (distinctOpen E I).ι := by
    rw [Scheme.Opens.range_ι]
    exact universalLift_range_distinct E I a ha
  let b := IsOpenImmersion.lift (distinctOpen E I).ι (lift E I a).left hr
  refine Over.homMk b ?_
  change b ≫ (distinctOpen E I).ι ≫ (tuples E I).hom = T.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact (lift E I a).w

/-- The lift keeps the entire original tuple after the actual open inclusion. -/
@[reassoc] theorem universalDistinctLift_inclusion :
    universalDistinctLift E I a ha ≫ distinctInclusion E I = lift E I a := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Every original coordinate is retained on arbitrary further scheme tests. -/
@[reassoc (attr := simp)] theorem universalDistinctLift_coordinate (i : I) :
    universalDistinctLift E I a ha ≫ distinctCoordinate E I i = a i := by
  rw [distinctCoordinate, ← Category.assoc, universalDistinctLift_inclusion, lift_coordinate]

end FLT.Mazur.RelativeOrderedTuples
