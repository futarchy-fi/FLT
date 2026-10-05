/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePicardGroup
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Pullback on scheme Picard groups

Actual sheaf pullback induces a contravariant group-valued functor. The
identity and composition laws follow from the existing pullback isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace FLT.Mazur.SchemePicard

open FCurve

variable {X Y Z : Scheme.{u}}

/-- Pullback of isomorphism classes along a scheme morphism. -/
def pullback (f : X ⟶ Y) : Pic Y →* Pic X where
  toFun a := Quotient.liftOn a
    (fun M ↦ mk ((Scheme.Modules.pullback f).obj M.val) (M.property.pullback f))
    (fun _ _ ⟨e⟩ ↦ mk_eq_of_iso _ _ ((Scheme.Modules.pullback f).mapIso e))
  map_one' := mk_eq_of_iso _ _ (modulePullbackUnitIso f)
  map_mul' a b := by
    induction a using inductionOn with | h M hM =>
      induction b using inductionOn with | h N hN =>
        exact mk_eq_of_iso _ _ (ModuleLineBundleTensorPullback.tensorIso f M N)

/-- Pullback of a class is represented by the actual pullback sheaf. -/
@[simp]
theorem pullback_mk (f : X ⟶ Y) (M : Y.Modules) (hM : LocallyFreeRankOne M) :
    pullback f (mk M hM) = mk ((Scheme.Modules.pullback f).obj M) (hM.pullback f) := rfl

/-- The identity scheme morphism induces the identity on Picard groups. -/
@[simp]
theorem pullback_id (a : Pic X) : pullback (𝟙 X) a = a := by
  induction a using inductionOn with | h M hM =>
    exact mk_eq_of_iso _ _ ((Scheme.Modules.pullbackId X).app M)

/-- Composition of scheme morphisms reverses the order of Picard pullbacks. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a : Pic Z) :
    pullback (f ≫ g) a = pullback f (pullback g a) := by
  induction a using inductionOn with | h M hM =>
    exact mk_eq_of_iso _ _ ((Scheme.Modules.pullbackComp f g).app M).symm

/-- The Picard group is a contravariant functor on schemes. -/
def functor : Scheme.{u}ᵒᵖ ⥤ CommGrpCat where
  obj X := CommGrpCat.of (Pic X.unop)
  map f := CommGrpCat.ofHom (pullback f.unop)
  map_id X := by ext a; exact pullback_id a
  map_comp f g := by ext a; exact pullback_comp g.unop f.unop a

/-- Picard pullbacks agree around every commuting square. -/
theorem pullback_square {W : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ W) (i : X ⟶ Z) (j : Y ⟶ W)
    (h : f ≫ j = i ≫ g) (a : Pic W) :
    pullback f (pullback j a) = pullback i (pullback g a) := by
  rw [← pullback_comp, h, pullback_comp]

/-- A section of a morphism splits its pullback on Picard groups. -/
theorem pullback_section (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y)
    (a : Pic Y) : pullback e (pullback f a) = a := by
  rw [← pullback_comp, he, pullback_id]

/-- Base pullback is injective when the morphism has a section. -/
theorem pullback_injective_of_section (f : X ⟶ Y) (e : Y ⟶ X)
    (he : e ≫ f = 𝟙 Y) : Function.Injective (pullback f) :=
  Function.LeftInverse.injective (pullback_section f e he)

end FLT.Mazur.SchemePicard
