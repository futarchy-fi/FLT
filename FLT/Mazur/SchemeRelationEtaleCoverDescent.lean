/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationReanchoring
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Descending full relation invariants along etale source covers

An etale source atlas does not have to be an open immersion. Its full relation
invariants descend to the original source as actual scheme morphisms. Both
endpoints are covered independently when testing the descended relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationEtaleCoverDescent
open SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false

variable {D A B : Scheme.{u}} (p q : D ⟶ A) (b : B ⟶ A)

instance arrow_etale [Etale b] : Etale (arrow p q b) :=
  inferInstanceAs (Etale
    (pullback.fst (pullback.fst p b ≫ q) b ≫ pullback.fst p b))

instance arrow_surjective [Surjective b] : Surjective (arrow p q b) :=
  inferInstanceAs (Surjective
    (pullback.fst (pullback.fst p b ≫ q) b ≫ pullback.fst p b))

variable {S Z : Scheme.{u}} {E X : Over S} {r t : E ⟶ X}
  (e : CategoryTheory.EquivalenceRelation r t) (k : Z ⟶ X.left)
  {Q : Scheme.{u}} (v : Z ⟶ Q)
local notation "x" => fst r.left t.left k
local notation "y" => snd r.left t.left k

include e in
/-- Reflexivity makes every full relation invariant compatible with the atlas kernel. -/
theorem kernel_compatible (hv : x ≫ v = y ≫ v)
    {Y : Scheme.{u}} (a b : Y ⟶ Z) (hab : a ≫ k = b ≫ k) : a ≫ v = b ≫ v := by
  let c := lift r.left t.left k ((a ≫ k) ≫ e.r.left) a b
    (by
      rw [Category.assoc, show e.r.left ≫ r.left = 𝟙 X.left from
        congrArg Over.Hom.left e.reflexivity₁, Category.comp_id])
    (by
      rw [Category.assoc, show e.r.left ≫ t.left = 𝟙 X.left from
        congrArg Over.Hom.left e.reflexivity₂, Category.comp_id, hab])
  have h := congrArg (fun z ↦ c ≫ z) hv
  simpa only [← Category.assoc, c, lift_fst, lift_snd] using h

variable [Etale k] [Surjective k]

/-- The invariant atlas morphism descends on the original scheme, including its sheaf map. -/
def descend (hv : x ≫ v = y ≫ v) : X.left ⟶ Q :=
  EffectiveEpi.desc k v (kernel_compatible e k v hv)

@[reassoc]
theorem cover_descend (hv : x ≫ v = y ≫ v) : k ≫ descend e k v hv = v :=
  EffectiveEpi.fac k v _

/-- Covering both endpoints detects invariance for every original relation arrow. -/
theorem descend_invariant (hv : x ≫ v = y ≫ v) :
    r.left ≫ descend e k v hv = t.left ≫ descend e k v hv := by
  apply (cancel_epi (arrow r.left t.left k)).mp
  rw [← Category.assoc, ← Category.assoc, arrow_fst, arrow_snd,
    Category.assoc, Category.assoc, cover_descend]
  exact hv

/-- Descent is unique among scheme maps, not just on points. -/
theorem descend_unique (hv : x ≫ v = y ≫ v) (w : X.left ⟶ Q) (hw : k ≫ w = v) :
    w = descend e k v hv := (cancel_epi k).mp (hw.trans (cover_descend e k v hv).symm)

/-- Every original coefficient morphism is retained by the descent. -/
@[reassoc]
theorem descend_ground (hv : x ≫ v = y ≫ v) {T : Scheme.{u}}
    (i : Q ⟶ T) (a : X.left ⟶ T) (hi : v ≫ i = k ≫ a) :
    descend e k v hv ≫ i = a := by
  apply (cancel_epi k).mp
  rw [cover_descend_assoc, hi]

end FLT.Mazur.SchemeRelationEtaleCoverDescent
