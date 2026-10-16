/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDistinctEtale

/-!
# Constructing ordered-point tests from distinct original sections

On a one-point test scheme, an injective tuple of original sections avoids
all collision equalizers, since those equalizers are open. The tuple therefore
lifts to the constructed distinct-point scheme, retaining every coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {T : Over S} [Subsingleton T.left]
  (a : I → (T ⟶ E)) (ha : Function.Injective a)

include ha in
/-- An injective tuple on a one-point test avoids every actual collision locus. -/
theorem lift_range_distinct :
    Set.range (lift E I a).left ⊆ (distinctOpen E I : Set (tuples E I).left) := by
  rintro _ ⟨x, rfl⟩
  apply (mem_distinctOpen E I _).mpr
  intro i j hij hc
  change (lift E I a).left x ∈ Set.range (collisionInclusion E I i j).left at hc
  have hr : Set.range (lift E I a).left ⊆ Set.range (collisionInclusion E I i j).left := by
    rintro _ ⟨y, rfl⟩
    simpa only [Subsingleton.elim y x] using hc
  let z := IsOpenImmersion.lift (collisionInclusion E I i j).left (lift E I a).left hr
  have hz : z ≫ (collisionInclusion E I i j).left = (lift E I a).left :=
    IsOpenImmersion.lift_fac _ _ _
  apply hij
  apply ha
  apply Over.OverMorphism.ext
  have h := congrArg (fun m ↦ z ≫ m.left) (collision_condition E I i j)
  change z ≫ (collisionInclusion E I i j).left ≫ (coordinate E I i).left =
    z ≫ (collisionInclusion E I i j).left ≫ (coordinate E I j).left at h
  rw [← Category.assoc, ← Category.assoc, hz] at h
  have hi := congrArg Over.Hom.left (lift_coordinate E I a i)
  have hj := congrArg Over.Hom.left (lift_coordinate E I a j)
  exact hi.symm.trans (h.trans hj)

/-- The actual lift of the injectively labeled original sections to the distinct-point scheme. -/
def distinctLift : T ⟶ distinctScheme E I := by
  have hr : Set.range (lift E I a).left ⊆ Set.range (distinctOpen E I).ι := by
    rw [Scheme.Opens.range_ι]
    exact lift_range_distinct E I a ha
  let b : T.left ⟶ (distinctOpen E I).toScheme :=
    IsOpenImmersion.lift (distinctOpen E I).ι (lift E I a).left hr
  refine Over.homMk b ?_
  change b ≫ (distinctOpen E I).ι ≫ (tuples E I).hom = T.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact (lift E I a).w

/-- The lift is the original tuple after its actual open inclusion. -/
@[reassoc] theorem distinctLift_inclusion :
    distinctLift E I a ha ≫ distinctInclusion E I = lift E I a := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Every original coordinate is retained by the constructed lift. -/
@[reassoc (attr := simp)] theorem distinctLift_coordinate (i : I) :
    distinctLift E I a ha ≫ distinctCoordinate E I i = a i := by
  rw [distinctCoordinate, ← Category.assoc, distinctLift_inclusion, lift_coordinate]

omit [Subsingleton T.left] [Etale E.hom] in
/-- Lifts to the distinct-point scheme are uniquely determined by all original coordinates. -/
theorem distinct_hom_ext {b c : T ⟶ distinctScheme E I}
    (h : ∀ i, b ≫ distinctCoordinate E I i = c ≫ distinctCoordinate E I i) : b = c := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (distinctOpen E I).ι).mp
  have hh : b ≫ distinctInclusion E I = c ≫ distinctInclusion E I := by
    apply hom_ext
    intro i
    simpa only [Category.assoc, distinctCoordinate] using h i
  exact congrArg Over.Hom.left hh

end FLT.Mazur.RelativeOrderedTuples
