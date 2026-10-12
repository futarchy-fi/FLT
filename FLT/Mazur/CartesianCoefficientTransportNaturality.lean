/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianCoefficientTransport

/-!
# Naturality of transport on actual coefficient overlaps

Transport commutes with morphisms of Cartesian objects and with restriction
of the overlap. These equalities retain the original object projections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.CartesianCoefficientTransport
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {B S X Y T : C} {p : Y ⟶ X} {s : Y ⟶ S} {f : X ⟶ B} {q : S ⟶ B}
  (H : IsPullback p s f q) (r t : T ⟶ S) (h : r ≫ q = t ≫ q)

/-- Restrict a coefficient pullback along a map of overlap schemes. -/
def restrict {U : C} (k : U ⟶ T) : pullback (k ≫ r) s ⟶ pullback r s :=
  pullback.lift (pullback.fst (k ≫ r) s ≫ k) (pullback.snd (k ≫ r) s) (by
    rw [Category.assoc]
    exact pullback.condition)

@[reassoc (attr := simp)] theorem restrict_coefficient {U : C} (k : U ⟶ T) :
    restrict (s := s) r k ≫ pullback.fst r s = pullback.fst (k ≫ r) s ≫ k :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem restrict_object {U : C} (k : U ⟶ T) :
    restrict (s := s) r k ≫ pullback.snd r s = pullback.snd (k ≫ r) s :=
  pullback.lift_snd _ _ _

/-- Transport on a triple overlap restricts the same transport on the double overlap. -/
@[reassoc] theorem map_restrict {U : C} (k : U ⟶ T) :
    map H (k ≫ r) (k ≫ t) (by simp only [Category.assoc, h]) ≫ restrict t k =
      restrict r k ≫ map H r t h := by
  apply hom_ext H t <;> simp

variable {X' Y' : C} {p' : Y' ⟶ X'} {s' : Y' ⟶ S} {f' : X' ⟶ B}
  (H' : IsPullback p' s' f' q) (a : Y ⟶ Y') (b : X ⟶ X')
  (hp : a ≫ p' = p ≫ b) (hs : a ≫ s' = s)

/-- A morphism of objects induces the actual morphism of their coefficient pullbacks. -/
def objectMap : pullback r s ⟶ pullback r s' :=
  pullback.lift (pullback.fst r s) (pullback.snd r s ≫ a) (by
    rw [Category.assoc, hs]
    exact pullback.condition)

@[reassoc (attr := simp)] theorem objectMap_coefficient :
    objectMap r a hs ≫ pullback.fst r s' = pullback.fst r s :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem objectMap_object :
    objectMap r a hs ≫ pullback.snd r s' = pullback.snd r s ≫ a :=
  pullback.lift_snd _ _ _

include hp in
/-- In particular, an integral action commutes with overlap transport of its input domain. -/
@[reassoc] theorem map_naturality :
    map H r t h ≫ objectMap t a hs = objectMap r a hs ≫ map H' r t h := by
  apply hom_ext H' t
  · simp
  · simp only [Category.assoc, objectMap_object_assoc, hp, map_original_assoc,
      map_original]

end FLT.Mazur.CartesianCoefficientTransport
