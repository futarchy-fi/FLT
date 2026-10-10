/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentPairNormalization
public import FLT.Mazur.SchemeFamilyTripleOverlap

/-!
# Cocycle laws on original unequal triple overlaps

Three independent modules and their original pair isomorphisms give three
normalized maps on the original triple. Compatible source isomorphisms
preserve and detect their composition law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentTripleCocycle
open SchemeFamilyTripleOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y₁ Y₂ Y₃ : Scheme.{u}} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (h : Y₃ ⟶ X)
variable (M₁ : Y₁.Modules) (M₂ : Y₂.Modules) (M₃ : Y₃.Modules)

/-- The first supplied pair isomorphism, normalized on the original triple. -/
def edge12 (e : (pullback (Limits.pullback.fst f g)).obj M₁ ≅
    (pullback (Limits.pullback.snd f g)).obj M₂) :
    (pullback (coord1 f g h)).obj M₁ ≅ (pullback (coord2 f g h)).obj M₂ :=
  SchemeIndependentPairNormalization.normalize _ _ (pair12 f g h) _ _ rfl rfl M₁ M₂ e

/-- The second supplied pair isomorphism, normalized at the common middle coordinate. -/
def edge23 (e : (pullback (Limits.pullback.fst g h)).obj M₂ ≅
    (pullback (Limits.pullback.snd g h)).obj M₃) :
    (pullback (coord2 f g h)).obj M₂ ≅ (pullback (coord3 f g h)).obj M₃ :=
  SchemeIndependentPairNormalization.normalize _ _ (pair23 f g h) _ _
    (pair23_fst f g h) rfl M₂ M₃ e

/-- The outer supplied pair isomorphism, normalized on the original triple. -/
def edge13 (e : (pullback (Limits.pullback.fst f h)).obj M₁ ≅
    (pullback (Limits.pullback.snd f h)).obj M₃) :
    (pullback (coord1 f g h)).obj M₁ ≅ (pullback (coord3 f g h)).obj M₃ :=
  SchemeIndependentPairNormalization.normalize _ _ (pair13 f g h) _ _
    (pair13_fst f g h) (pair13_snd f g h) M₁ M₃ e

/-- The cocycle equation uses only the original modules and unequal pairwise overlaps. -/
def Cocycle
    (e12 : (pullback (Limits.pullback.fst f g)).obj M₁ ≅
      (pullback (Limits.pullback.snd f g)).obj M₂)
    (e23 : (pullback (Limits.pullback.fst g h)).obj M₂ ≅
      (pullback (Limits.pullback.snd g h)).obj M₃)
    (e13 : (pullback (Limits.pullback.fst f h)).obj M₁ ≅
      (pullback (Limits.pullback.snd f h)).obj M₃) : Prop :=
  (edge12 f g h M₁ M₂ e12).hom ≫ (edge23 f g h M₂ M₃ e23).hom =
    (edge13 f g h M₁ M₃ e13).hom

/-- Composition laws are detected by compatible isomorphisms of all three coordinates. -/
lemma comp_of_coordinateIso {C : Type*} [Category C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}
    (a₁ : A₁ ≅ B₁) (a₂ : A₂ ≅ B₂) (a₃ : A₃ ≅ B₃)
    (e12 : A₁ ⟶ A₂) (e23 : A₂ ⟶ A₃) (e13 : A₁ ⟶ A₃)
    (e12' : B₁ ⟶ B₂) (e23' : B₂ ⟶ B₃) (e13' : B₁ ⟶ B₃)
    (h12 : e12 ≫ a₂.hom = a₁.hom ≫ e12')
    (h23 : e23 ≫ a₃.hom = a₂.hom ≫ e23')
    (h13 : e13 ≫ a₃.hom = a₁.hom ≫ e13') (hc : e12' ≫ e23' = e13') :
    e12 ≫ e23 = e13 := by
  apply (cancel_mono a₃.hom).mp
  rw [Category.assoc, h23, ← Category.assoc, h12, Category.assoc, hc, h13]

/-- Compatible isomorphisms of the three original source modules detect their cocycle. -/
lemma cocycle_of_sourceIso {N₁ : Y₁.Modules} {N₂ : Y₂.Modules} {N₃ : Y₃.Modules}
    (a₁ : M₁ ≅ N₁) (a₂ : M₂ ≅ N₂) (a₃ : M₃ ≅ N₃)
    (e12 : (pullback (Limits.pullback.fst f g)).obj M₁ ≅
      (pullback (Limits.pullback.snd f g)).obj M₂)
    (e23 : (pullback (Limits.pullback.fst g h)).obj M₂ ≅
      (pullback (Limits.pullback.snd g h)).obj M₃)
    (e13 : (pullback (Limits.pullback.fst f h)).obj M₁ ≅
      (pullback (Limits.pullback.snd f h)).obj M₃)
    (e12' : (pullback (Limits.pullback.fst f g)).obj N₁ ≅
      (pullback (Limits.pullback.snd f g)).obj N₂)
    (e23' : (pullback (Limits.pullback.fst g h)).obj N₂ ≅
      (pullback (Limits.pullback.snd g h)).obj N₃)
    (e13' : (pullback (Limits.pullback.fst f h)).obj N₁ ≅
      (pullback (Limits.pullback.snd f h)).obj N₃)
    (h12 : e12.hom ≫ (pullback (Limits.pullback.snd f g)).map a₂.hom =
      (pullback (Limits.pullback.fst f g)).map a₁.hom ≫ e12'.hom)
    (h23 : e23.hom ≫ (pullback (Limits.pullback.snd g h)).map a₃.hom =
      (pullback (Limits.pullback.fst g h)).map a₂.hom ≫ e23'.hom)
    (h13 : e13.hom ≫ (pullback (Limits.pullback.snd f h)).map a₃.hom =
      (pullback (Limits.pullback.fst f h)).map a₁.hom ≫ e13'.hom)
    (hc : Cocycle f g h N₁ N₂ N₃ e12' e23' e13') :
    Cocycle f g h M₁ M₂ M₃ e12 e23 e13 :=
  comp_of_coordinateIso ((pullback (coord1 f g h)).mapIso a₁)
    ((pullback (coord2 f g h)).mapIso a₂) ((pullback (coord3 f g h)).mapIso a₃)
    _ _ _ _ _ _
    (SchemeIndependentPairNormalization.normalize_compatible _ _ (pair12 f g h)
      _ _ rfl rfl e12 e12' a₁.hom a₂.hom h12)
    (SchemeIndependentPairNormalization.normalize_compatible _ _ (pair23 f g h)
      _ _ (pair23_fst f g h) rfl e23 e23' a₂.hom a₃.hom h23)
    (SchemeIndependentPairNormalization.normalize_compatible _ _ (pair13 f g h)
      _ _ (pair13_fst f g h) (pair13_snd f g h) e13 e13' a₁.hom a₃.hom h13) hc

end FLT.Mazur.SchemeIndependentTripleCocycle
