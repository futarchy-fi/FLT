/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationEtaleCoverDescent

/-!
# Recovering the full original kernel from an etale source atlas

Cover both coordinates of the candidate kernel independently. The atlas
kernel constructs an original arrow on that cover. Effective epimorphism
descent then constructs its inverse on the entire original scheme kernel.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationEtaleKernelDescent
open SchemeRelationRestriction SchemeRelationEtaleCoverDescent
set_option backward.isDefEq.respectTransparency false
variable {D A B Q : Scheme.{u}} (p q : D ⟶ A) (k : B ⟶ A) (w : A ⟶ Q)
  (h : p ≫ w = q ≫ w)
  (H : IsPullback (fst p q k) (snd p q k) (k ≫ w) (k ≫ w))
local notation "m" => pullback.lift p q h
local notation "a" => pullback.fst w w
local notation "b" => pullback.snd w w
local notation "C" => doubleDomain a b k
local notation "x" => fst a b k
local notation "y" => snd a b k
local notation "c" => arrow a b k

/-- The complete candidate kernel is covered in both coordinates, without a diagonal constraint. -/
theorem cover_condition : x ≫ (k ≫ w) = y ≫ (k ≫ w) := by
  rw [← Category.assoc, ← Category.assoc, ← arrow_fst, ← arrow_snd]
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- Construct the original relation arrow on the full two-coordinate atlas of the kernel. -/
def localArrow : C ⟶ D := H.lift x y (cover_condition k w) ≫ arrow p q k

@[reassoc]
theorem localArrow_fst : localArrow p q k w H ≫ p = x ≫ k := by
  rw [localArrow, Category.assoc, arrow_fst, H.lift_fst_assoc]

@[reassoc]
theorem localArrow_snd : localArrow p q k w H ≫ q = y ≫ k := by
  rw [localArrow, Category.assoc, arrow_snd, H.lift_snd_assoc]

/-- The constructed arrow lifts the actual cover morphism, including all nilpotents. -/
@[reassoc]
theorem localArrow_comparison : localArrow p q k w H ≫ m = c := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, localArrow_fst, arrow_fst]
  · rw [Category.assoc, pullback.lift_snd, localArrow_snd, arrow_snd]

variable [Mono (pullback.lift p q h)]

include h in
/-- The monomorphic original comparison makes the locally constructed arrow compatible. -/
theorem localArrow_compatible {Y : Scheme.{u}} (f g : Y ⟶ C)
    (hfg : f ≫ c = g ≫ c) :
    f ≫ localArrow p q k w H = g ≫ localArrow p q k w H := by
  apply (cancel_mono m).mp
  simpa only [Category.assoc, localArrow_comparison] using hfg

variable [Etale k] [Surjective k]

/-- Descend the original arrow to every test of the unrestricted original kernel. -/
def inverse : pullback w w ⟶ D :=
  EffectiveEpi.desc c (localArrow p q k w H) (localArrow_compatible p q k w h H)

@[reassoc]
theorem cover_inverse : c ≫ inverse p q k w h H = localArrow p q k w H :=
  EffectiveEpi.fac c _ _

@[reassoc]
theorem inverse_comparison : inverse p q k w h H ≫ m = 𝟙 _ := by
  apply (cancel_epi c).mp
  rw [cover_inverse_assoc, localArrow_comparison, Category.comp_id]

@[reassoc]
theorem comparison_inverse : m ≫ inverse p q k w h H = 𝟙 _ := by
  apply (cancel_mono m).mp
  rw [Category.assoc, inverse_comparison, Category.comp_id, Category.id_comp]

/-- The full original relation is isomorphic to its original candidate kernel. -/
def kernelIso : D ≅ pullback w w where
  hom := m
  inv := inverse p q k w h H
  hom_inv_id := comparison_inverse p q k w h H
  inv_hom_id := inverse_comparison p q k w h H

include h H in
/-- Full scheme-kernel effectivity descends from an etale source cover. -/
theorem isPullback : IsPullback p q w w :=
  IsPullback.of_iso_pullback ⟨h⟩ (kernelIso p q k w h H)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end FLT.Mazur.SchemeRelationEtaleKernelDescent
