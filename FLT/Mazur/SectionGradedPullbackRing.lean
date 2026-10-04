/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPullback
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Pullback of the full graded section ring

The ring homomorphism acts on every tensor degree by the actual adjunction
unit followed by the tensor-power pullback comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedPullback
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)

/-- Pullback on the full additive direct sum. -/
def sumMap : SectionGradedSum.Sections L ⊤ →+ SectionGradedSum.Sections ((pullback f).obj L) ⊤ :=
  DirectSum.toAddMonoid (fun n ↦ (DirectSum.of (Piece ((pullback f).obj L) ⊤) n).comp
    ((powerMap f L n).app ⊤).hom)

/-- The full pullback has the prescribed homogeneous components. -/
lemma sumMap_of (n : ℕ) (s : Piece L ⊤ n) :
    sumMap f L (of L ⊤ n s) = of ((pullback f).obj L) ⊤ n (pull f L n ⊤ s) :=
  DirectSum.toAddMonoid_of _ n s

/-- Pullback preserves products of arbitrary finite sums. -/
lemma sumMap_product (a b : SectionGradedSum.Sections L ⊤) :
    sumMap f L (product L ⊤ a b) =
      product ((pullback f).obj L) ⊤ (sumMap f L a) (sumMap f L b) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m s =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n t =>
      change sumMap f L (product L ⊤ (of L ⊤ m s) (of L ⊤ n t)) =
        product ((pullback f).obj L) ⊤ (sumMap f L (of L ⊤ m s)) (sumMap f L (of L ⊤ n t))
      rw [product_of, sumMap_of, sumMap_of, sumMap_of, product_of, pull_mul]
      rfl
    | add b c hb hc => simp only [map_add, hb, hc]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]

/-- Pullback is a unital homomorphism of the actual section rings. -/
def ringHom : SectionGradedSum.Sections L ⊤ →+*
    SectionGradedSum.Sections ((pullback f).obj L) ⊤ where
  __ := sumMap f L
  map_one' := by
    change sumMap f L (of L ⊤ 0 (1 : Γ(Y, ⊤))) =
      of ((pullback f).obj L) ⊤ 0 (1 : Γ(X, ⊤))
    rw [sumMap_of, pull_zero, map_one]
  map_mul' a b := by
    simp only [mul_eq_product]
    exact sumMap_product f L a b

/-- The ring pullback preserves each actual homogeneous submodule. -/
lemma ringHom_mem_grade {n : ℕ} {s : SectionGradedSum.Sections L ⊤} (hs : s ∈ grade L ⊤ n) :
    ringHom f L s ∈ grade ((pullback f).obj L) ⊤ n := by
  obtain ⟨t, rfl⟩ := hs
  exact ⟨pull f L n ⊤ t, (sumMap_of f L n t).symm⟩

/-- The full section-ring pullback bundled as a graded ring homomorphism. -/
def gradedRingHom : grade L ⊤ →+*ᵍ grade ((pullback f).obj L) ⊤ where
  __ := ringHom f L
  map_mem := fun hs ↦ ringHom_mem_grade f L hs

end FLT.Mazur.SectionGradedPullback
