/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationArrowCalculus

/-!
# Transporting full relation arrows between independent seeds

Two arrows from arbitrary source endpoints to arbitrary seed endpoints transport
relations in both directions. The seed endpoints need not coincide. All
constructions are scheme morphisms, so they retain nonreduced test schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Original relation arrows are determined by their endpoints on any scheme test. -/
theorem originalArrow_ext {Y : Scheme.{u}} {a b : Y ⟶ D.left}
    (hp : a ≫ p.left = b ≫ p.left) (hq : a ≫ q.left = b ≫ q.left) : a = b := by
  let Y' : Over S := Over.mk (a ≫ D.hom)
  let a' : Y' ⟶ D := Over.homMk a
  let b' : Y' ⟶ D := Over.homMk b (by
    change b ≫ D.hom = a ≫ D.hom
    rw [← p.w, ← Category.assoc, ← hp, Category.assoc])
  exact congrArg Over.Hom.left (e.toJointlyMono₂.right_cancellation a' b'
    (Over.OverMorphism.ext hp) (Over.OverMorphism.ext hq))

variable {Y : Scheme.{u}} (a b z : Y ⟶ D.left)

/-- Move a relation between source endpoints to a relation between the two seed endpoints. -/
def transportOriginal (hp : z ≫ p.left = a ≫ p.left)
    (hq : z ≫ q.left = b ≫ p.left) : Y ⟶ D.left :=
  composeOriginal e (a ≫ e.s.left) (composeOriginal e z b hq) (by
    rw [Category.assoc, ← Over.comp_left, e.symmetry₂, composeOriginal_fst]
    exact hp.symm)

@[reassoc]
theorem transportOriginal_fst (hp : z ≫ p.left = a ≫ p.left)
    (hq : z ≫ q.left = b ≫ p.left) :
    transportOriginal e a b z hp hq ≫ p.left = a ≫ q.left := by
  rw [transportOriginal, composeOriginal_fst, Category.assoc,
    ← Over.comp_left, e.symmetry₁]

@[reassoc]
theorem transportOriginal_snd (hp : z ≫ p.left = a ≫ p.left)
    (hq : z ≫ q.left = b ≫ p.left) :
    transportOriginal e a b z hp hq ≫ q.left = b ≫ q.left := by
  rw [transportOriginal, composeOriginal_snd, composeOriginal_snd]

/-- Recover the relation between source endpoints from an arbitrary seed relation. -/
def untransportOriginal (hp : z ≫ p.left = a ≫ q.left)
    (hq : z ≫ q.left = b ≫ q.left) : Y ⟶ D.left :=
  composeOriginal e a (divideOriginal e z b hq) (by
    rw [divideOriginal_fst]
    exact hp.symm)

@[reassoc]
theorem untransportOriginal_fst (hp : z ≫ p.left = a ≫ q.left)
    (hq : z ≫ q.left = b ≫ q.left) :
    untransportOriginal e a b z hp hq ≫ p.left = a ≫ p.left :=
  composeOriginal_fst e _ _ _

@[reassoc]
theorem untransportOriginal_snd (hp : z ≫ p.left = a ≫ q.left)
    (hq : z ≫ q.left = b ≫ q.left) :
    untransportOriginal e a b z hp hq ≫ q.left = b ≫ p.left := by
  rw [untransportOriginal, composeOriginal_snd, divideOriginal_snd]

/-- Transport followed by recovery preserves the literal original relation arrow. -/
theorem untransport_transportOriginal (hp : z ≫ p.left = a ≫ p.left)
    (hq : z ≫ q.left = b ≫ p.left) :
    untransportOriginal e a b (transportOriginal e a b z hp hq)
      (transportOriginal_fst e a b z hp hq)
      (transportOriginal_snd e a b z hp hq) = z := by
  apply originalArrow_ext e
  · exact (untransportOriginal_fst e _ _ _ _ _).trans hp.symm
  · exact (untransportOriginal_snd e _ _ _ _ _).trans hq.symm

/-- Recovery followed by transport preserves the full seed relation arrow. -/
theorem transport_untransportOriginal (hp : z ≫ p.left = a ≫ q.left)
    (hq : z ≫ q.left = b ≫ q.left) :
    transportOriginal e a b (untransportOriginal e a b z hp hq)
      (untransportOriginal_fst e a b z hp hq)
      (untransportOriginal_snd e a b z hp hq) = z := by
  apply originalArrow_ext e
  · exact (transportOriginal_fst e _ _ _ _ _).trans hp.symm
  · exact (transportOriginal_snd e _ _ _ _ _).trans hq.symm

end FLT.Mazur.RelativeRelationOrbit
