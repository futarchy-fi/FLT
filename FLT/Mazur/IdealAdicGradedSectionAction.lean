/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedSections

/-!
# Homogeneous sections act on the actual graded sheaves

Multiplication by a global homogeneous section defines a sheaf morphism,
not just a map on global sections. Its composition law is the actual
associativity identity, with the required degree transport.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- Restrict a homogeneous global section to an arbitrary open. -/
def globalRestrict (a : ℕ) (U : X.Opens) : Piece I ⊤ a →+ Piece I U a :=
  ((idealGraded I a).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom

omit [IsLocallyNoetherian X] in
/-- Restricting a homogeneous global section twice is the direct restriction. -/
lemma globalRestrict_res (a : ℕ) {U V : X.Opens} (i : U ⟶ V) (s : Piece I ⊤ a) :
    (idealGraded I a).presheaf.map i.op (globalRestrict I a V s) =
      globalRestrict I a U s := by
  change ((idealGraded I a).presheaf.map _ ≫ (idealGraded I a).presheaf.map _) s = _
  rw [← Functor.map_comp]
  rfl

/-- A homogeneous global coefficient acts on each graded sheaf. -/
def sectionAction (a n : ℕ) (s : Piece I ⊤ a) :
    idealGraded I n ⟶ idealGraded I (a + n) :=
  ⟨{ app U := ModuleCat.ofHom (mul I U.unop a n (globalRestrict I a U.unop s))
     naturality {U V} i := by
       ext t
       have h := mul_restrict I i.unop a n (globalRestrict I a U.unop s) t
       rw [globalRestrict_res] at h
       exact h.symm }⟩

/-- The sheaf action is the actual graded product on every open. -/
lemma sectionAction_app (a n : ℕ) (s : Piece I ⊤ a) (U : X.Opens) (t : Piece I U n) :
    (sectionAction I a n s).app U t = mul I U a n (globalRestrict I a U s) t := rfl

/-- Global restriction respects homogeneous multiplication. -/
lemma globalRestrict_mul (a b : ℕ) (U : X.Opens) (s : Piece I ⊤ a) (t : Piece I ⊤ b) :
    globalRestrict I (a + b) U (mul I ⊤ a b s t) =
      mul I U a b (globalRestrict I a U s) (globalRestrict I b U t) :=
  mul_restrict I (homOfLE le_top) a b s t

/-- Multiplying coefficients composes their sheaf actions with the degree transport. -/
lemma sectionAction_mul (a b n : ℕ) (s : Piece I ⊤ a) (t : Piece I ⊤ b) :
    sectionAction I (a + b) n (mul I ⊤ a b s t) =
      sectionAction I b n t ≫ sectionAction I a (b + n) s ≫
        idealGradedReindex I (Nat.add_assoc a b n).symm := by
  apply Scheme.Modules.hom_ext
  intro U
  ext v
  change mul I U (a + b) n (globalRestrict I (a + b) U (mul I ⊤ a b s t)) v =
    cast I (Nat.add_assoc a b n).symm U
      (mul I U a (b + n) (globalRestrict I a U s)
        (mul I U b n (globalRestrict I b U t) v))
  rw [globalRestrict_mul]
  exact mul_assoc I a b n U _ _ v

/-- The degree-zero unit acts identically after the canonical degree transport. -/
lemma sectionAction_unit (n : ℕ) :
    sectionAction I 0 n (scalar I ⊤ 1) ≫ idealGradedReindex I (Nat.zero_add n) =
      𝟙 (idealGraded I n) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext t
  change cast I (Nat.zero_add n) U
    (mul I U 0 n (globalRestrict I 0 U (scalar I ⊤ 1)) t) = t
  have hs : globalRestrict I 0 U (scalar I ⊤ 1) = scalar I U 1 := by
    exact (scalar_restrict I (homOfLE le_top) 1).trans
      (congrArg (scalar I U) ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.map_one))
  rw [hs, scalar_mul, one_smul]
  have hc (a b : ℕ) (h : a = b) (v : Piece I U b) :
      cast I h U (cast I h.symm U v) = v := by subst b; rfl
  exact hc _ _ _ t

/-- Adding homogeneous coefficients adds their sheaf actions. -/
lemma sectionAction_add (a n : ℕ) (s t : Piece I ⊤ a) :
    sectionAction I a n (s + t) = sectionAction I a n s + sectionAction I a n t := by
  apply Scheme.Modules.hom_ext
  intro U
  ext v
  change mul I U a n (globalRestrict I a U (s + t)) v =
    mul I U a n (globalRestrict I a U s) v + mul I U a n (globalRestrict I a U t) v
  rw [map_add, map_add, LinearMap.add_apply]

end FLT.Mazur.IdealAdicGradedSections
