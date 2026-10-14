/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationReanchoring

/-!
# Full kernels after factoring a source atlas

Factoring an atlas through an intermediate parameter scheme retains its full
original relation. A kernel on the atlas is therefore also the kernel for
the iterated restriction, without a monicity assumption on the factorization.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationNestedKernel
open SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {S B U Q : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (i : U ⟶ A.left) (k : B ⟶ A.left) (b : B ⟶ U) (hb : b ≫ i = k)
local notation "r" => fst p.left q.left i
local notation "t" => snd p.left q.left i
local notation "x" => fst r t b
local notation "y" => snd r t b
local notation "F" => doubleDomain p.left q.left k
local notation "G" => doubleDomain r t b

include e in
/-- Both final atlas endpoints determine the full iterated original arrow. -/
theorem endpoint_ext {Y : Scheme.{u}} (a c : Y ⟶ G)
    (hx : a ≫ x = c ≫ x) (hy : a ≫ y = c ≫ y) : a = c := by
  have ha : a ≫ arrow r t b = c ≫ arrow r t b := by
    apply SchemeRelationReanchoring.endpoint_ext e i
    · simpa only [Category.assoc, arrow_fst] using congrArg (fun z ↦ z ≫ b) hx
    · simpa only [Category.assoc, arrow_snd] using congrArg (fun z ↦ z ≫ b) hy
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact ha
    · exact hx
  · exact hy

/-- Recover the literal original arrow with its two independent final atlas endpoints. -/
def toOriginal : G ⟶ F := lift p.left q.left k
  (arrow r t b ≫ arrow p.left q.left i) x y
  (by rw [Category.assoc, arrow_fst, arrow_fst_assoc, hb])
  (by rw [Category.assoc, arrow_snd, arrow_snd_assoc, hb])

@[reassoc]
theorem toOriginal_fst : toOriginal i k b hb ≫ fst p.left q.left k = x :=
  lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem toOriginal_snd : toOriginal i k b hb ≫ snd p.left q.left k = y :=
  lift_snd _ _ _ _ _ _ _ _

/-- Lift an original full atlas arrow into the intermediate parameter relation. -/
def intermediate : F ⟶ doubleDomain p.left q.left i := lift p.left q.left i
  (arrow p.left q.left k) (fst p.left q.left k ≫ b) (snd p.left q.left k ≫ b)
  (by rw [Category.assoc, hb, arrow_fst])
  (by rw [Category.assoc, hb, arrow_snd])

/-- Keep both final lifts when passing through the intermediate source. -/
def fromOriginal : F ⟶ G := lift r t b (intermediate i k b hb)
  (fst p.left q.left k) (snd p.left q.left k)
  (lift_fst ..) (lift_snd ..)

@[reassoc]
theorem fromOriginal_fst : fromOriginal i k b hb ≫ x = fst p.left q.left k :=
  lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem fromOriginal_snd : fromOriginal i k b hb ≫ y = snd p.left q.left k :=
  lift_snd _ _ _ _ _ _ _ _

/-- The complete iterated relation and original atlas relation are scheme isomorphic. -/
def relationIso : G ≅ F where
  hom := toOriginal i k b hb
  inv := fromOriginal i k b hb
  hom_inv_id := by
    apply endpoint_ext e i b
    · rw [Category.assoc, fromOriginal_fst, toOriginal_fst, Category.id_comp]
    · rw [Category.assoc, fromOriginal_snd, toOriginal_snd, Category.id_comp]
  inv_hom_id := by
    apply SchemeRelationReanchoring.endpoint_ext e k
    · rw [Category.assoc, toOriginal_fst, fromOriginal_fst, Category.id_comp]
    · rw [Category.assoc, toOriginal_snd, fromOriginal_snd, Category.id_comp]

include e hb in
/-- An effective full atlas kernel remains effective for the intermediate-source relation. -/
theorem isPullback (v : B ⟶ Q)
    (H : IsPullback (fst p.left q.left k) (snd p.left q.left k) v v) :
    IsPullback x y v v := by
  apply H.of_iso' (relationIso e i k b hb) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [relationIso, Iso.refl_hom, Category.comp_id] using toOriginal_fst i k b hb
  · simpa only [relationIso, Iso.refl_hom, Category.comp_id] using toOriginal_snd i k b hb
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end FLT.Mazur.SchemeRelationNestedKernel
