/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedUnit

/-!
# Sections of the actual ideal-adic graded pieces

The product and unit are evaluated from the constructed sheaf morphisms.
Their laws hold on arbitrary opens, without a claim that sections of a
cokernel are quotients of sections on a nonaffine open.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve ModuleSheafTensor ModuleSheafTensorAssociator
open FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- Sections of the actual degree quotient sheaf. -/
abbrev Piece (U : X.Opens) (n : ℕ) : Type u := Γ(idealGraded I n, U)

/-- The actual graded sheaf multiplication, evaluated on sections. -/
def mul (U : X.Opens) (a b : ℕ) :
    Piece I U a →ₗ[Γ(X, U)] Piece I U b →ₗ[Γ(X, U)] Piece I U (a + b) :=
  ((pairing (idealGraded I a) (idealGraded I b)).app U).compr₂
    ((idealGradedMul I a b).val.app (.op U)).hom

/-- Structure scalars map to the actual degree-zero quotient. -/
def scalar (U : X.Opens) : Γ(X, U) →ₗ[Γ(X, U)] Piece I U 0 :=
  ((idealGradedUnit I).val.app (.op U)).hom

/-- Transport sections along equality of their degrees. -/
def cast {a b : ℕ} (h : a = b) (U : X.Opens) :
    Piece I U a →ₗ[Γ(X, U)] Piece I U b :=
  ((idealGradedReindex I h).val.app (.op U)).hom

omit [IsLocallyNoetherian X] in
/-- Reflexive transport fixes sections. -/
@[simp]
lemma cast_rfl (a : ℕ) (U : X.Opens) (s : Piece I U a) : cast I rfl U s = s := rfl

/-- Associativity retains the actual degree transport. -/
lemma mul_assoc (a b c : ℕ) (U : X.Opens)
    (s : Piece I U a) (t : Piece I U b) (v : Piece I U c) :
    mul I U (a + b) c (mul I U a b s t) v =
      cast I (Nat.add_assoc a b c).symm U (mul I U a (b + c) s (mul I U b c t v)) := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U (pure _ _ U s t) v))
    (idealGradedMul_assoc I a b c)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, associator_hom_pure] at h
  exact h

/-- Commutativity retains the actual degree transport. -/
lemma mul_comm (a b : ℕ) (U : X.Opens) (s : Piece I U a) (t : Piece I U b) :
    mul I U a b s t = cast I (Nat.add_comm b a) U (mul I U b a t s) := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U s t)) (idealGradedMul_comm I a b)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, comm_hom_pure] at h
  exact h

/-- Degree-zero scalars act by the given structure-module scalar action. -/
lemma scalar_mul (n : ℕ) (U : X.Opens) (r : Γ(X, U)) (s : Piece I U n) :
    mul I U 0 n (scalar I U r) s = cast I (Nat.zero_add n).symm U (r • s) := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U r s)) (idealGradedMul_unit_left I n)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply] at h
  have hu := leftUnitor_pure (idealGraded I n) U r s
  have hh : cast I (Nat.zero_add n) U (mul I U 0 n (scalar I U r) s) = r • s :=
    h.trans hu
  have hi (a b : ℕ) (e : a = b) (t : Piece I U a) :
      cast I e.symm U (cast I e U t) = t := by subst b; rfl
  exact (hi _ _ _ _).symm.trans (congrArg (cast I (Nat.zero_add n).symm U) hh)

/-- Right degree-zero multiplication is also scalar multiplication. -/
lemma mul_scalar (n : ℕ) (U : X.Opens) (s : Piece I U n) (r : Γ(X, U)) :
    mul I U n 0 s (scalar I U r) = r • s := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U s r)) (idealGradedMul_unit_right I n)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply] at h
  have hu := rightUnitor_pure (idealGraded I n) U r s
  exact h.trans hu

/-- The graded multiplication commutes with restriction. -/
lemma mul_restrict {U V : X.Opens} (i : U ⟶ V) (a b : ℕ)
    (s : Piece I V a) (t : Piece I V b) :
    (idealGraded I (a + b)).presheaf.map i.op (mul I V a b s t) =
      mul I U a b ((idealGraded I a).presheaf.map i.op s)
        ((idealGraded I b).presheaf.map i.op t) := by
  have h := congrArg (fun k ↦ k (pure (idealGraded I a) (idealGraded I b) V s t))
    ((idealGradedMul I a b).mapPresheaf.naturality i.op)
  change (idealGradedMul I a b).app U
    ((tensor (idealGraded I a) (idealGraded I b)).presheaf.map i.op
      (pure _ _ V s t)) = _ at h
  rw [pure_restrict] at h
  exact h.symm

omit [IsLocallyNoetherian X] in
/-- The degree-zero scalar map commutes with restriction. -/
lemma scalar_restrict {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, V)) :
    (idealGraded I 0).presheaf.map i.op (scalar I V r) =
      scalar I U (X.presheaf.map i.op r) :=
  (congrArg (fun k ↦ k r) ((idealGradedUnit I).mapPresheaf.naturality i.op)).symm

end FLT.Mazur.IdealAdicGradedSections
