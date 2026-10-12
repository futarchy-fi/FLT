/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianCoefficientSymmetry

/-!
# Transport between the two coefficient pullbacks of a Cartesian object

The transport keeps the original object projection. Its composition law
provides the cocycle on arbitrary coefficient overlaps, without choosing
branches or assuming a comparison isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.CartesianCoefficientTransport
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {B S X Y T : C} {p : Y ⟶ X} {s : Y ⟶ S} {f : X ⟶ B} {q : S ⟶ B}
  (H : IsPullback p s f q) (r t : T ⟶ S) (h : r ≫ q = t ≫ q)

/-- Change the chosen coefficient lift, retaining the original object. -/
def map : pullback r s ⟶ pullback t s :=
  pullback.lift (pullback.fst r s)
    (H.lift (pullback.snd r s ≫ p) (pullback.fst r s ≫ t) (by
      rw [Category.assoc, H.w, ← Category.assoc,
        ← pullback.condition (f := r) (g := s), Category.assoc, h, Category.assoc]))
    (by rw [H.lift_snd])

@[reassoc (attr := simp)] theorem map_coefficient :
    map H r t h ≫ pullback.fst t s = pullback.fst r s := pullback.lift_fst _ _ _

/-- The projection to the original object is unchanged, including on singular fibers. -/
@[reassoc (attr := simp)] theorem map_original :
    map H r t h ≫ pullback.snd t s ≫ p = pullback.snd r s ≫ p := by
  rw [map, pullback.lift_snd_assoc, H.lift_fst]

include H in
/-- These two retained projections determine maps to either iterated pullback. -/
theorem hom_ext {U : C} {a b : U ⟶ pullback r s}
    (hc : a ≫ pullback.fst r s = b ≫ pullback.fst r s)
    (hp : a ≫ pullback.snd r s ≫ p = b ≫ pullback.snd r s ≫ p) : a = b := by
  apply pullback.hom_ext hc
  apply H.hom_ext
  · simpa only [Category.assoc] using hp
  · calc
      (a ≫ pullback.snd r s) ≫ s = (a ≫ pullback.fst r s) ≫ r := by
        rw [Category.assoc, Category.assoc, pullback.condition]
      _ = (b ≫ pullback.fst r s) ≫ r := by rw [hc]
      _ = (b ≫ pullback.snd r s) ≫ s := by
        rw [Category.assoc, Category.assoc, pullback.condition]

/-- Identity transport is the actual identity morphism. -/
@[simp] theorem map_self : map H r r rfl = 𝟙 _ := by
  apply hom_ext H r <;> simp

/-- Transports compose on the entire iterated pullback, not just on coefficient points. -/
@[reassoc] theorem map_comp (w : T ⟶ S) (ht : t ≫ q = w ≫ q) :
    map H r t h ≫ map H t w ht = map H r w (h.trans ht) := by
  apply hom_ext H w <;> simp

/-- The canonical comparison is an isomorphism with reverse transport as inverse. -/
def iso : pullback r s ≅ pullback t s where
  hom := map H r t h
  inv := map H t r h.symm
  hom_inv_id := by rw [map_comp, map_self]
  inv_hom_id := by rw [map_comp, map_self]

end FLT.Mazur.CartesianCoefficientTransport
