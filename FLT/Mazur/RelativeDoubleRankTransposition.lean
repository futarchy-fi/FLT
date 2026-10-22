/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankUniversal

/-!
# Transposition of independent full rank charts

An endpoint involution lifts to the complete independent rank thickenings.
It exchanges both ranks and both infinitesimal orders. The resulting maps
are inverse on the full schemes, including their nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (τ : B ⟶ B) (hx : τ ≫ x = y) (hy : τ ≫ y = x)
  (n m r s : ℕ)

/-- Transpose the independent full stages over the given endpoint exchange. -/
def doubleRankTranspose :
    doubleRankThickening E x y n m r s ⟶ doubleRankThickening E x y m n s r :=
  doubleRankLift E x y m n s r (doubleRankMap E x y n m r s ≫ τ)
    (doubleRankSecond E x y n m r s) (doubleRankFirst E x y n m r s)
    (by rw [Category.assoc, hx]; exact doubleRankSecond_map E x y n m r s)
    (by rw [Category.assoc, hy]; exact doubleRankFirst_map E x y n m r s)

/-- Transposition preserves the original coefficient map up to the endpoint exchange. -/
@[reassoc (attr := simp)]
theorem doubleRankTranspose_map :
    doubleRankTranspose E x y τ hx hy n m r s ≫ doubleRankMap E x y m n s r =
      doubleRankMap E x y n m r s ≫ τ :=
  doubleRankLift_map _ _ _ _ _ _ _ _ _ _ _ _

/-- The full second coordinate becomes the first coordinate. -/
@[reassoc (attr := simp)]
theorem doubleRankTranspose_first :
    doubleRankTranspose E x y τ hx hy n m r s ≫ doubleRankFirst E x y m n s r =
      doubleRankSecond E x y n m r s :=
  doubleRankLift_first _ _ _ _ _ _ _ _ _ _ _ _

/-- The full first coordinate becomes the second coordinate. -/
@[reassoc (attr := simp)]
theorem doubleRankTranspose_second :
    doubleRankTranspose E x y τ hx hy n m r s ≫ doubleRankSecond E x y m n s r =
      doubleRankFirst E x y n m r s :=
  doubleRankLift_second _ _ _ _ _ _ _ _ _ _ _ _

/-- An involution on coefficients gives an involution on all full rank charts. -/
@[reassoc (attr := simp)]
theorem doubleRankTranspose_twice (hτ : τ ≫ τ = 𝟙 B) :
    doubleRankTranspose E x y τ hx hy n m r s ≫
      doubleRankTranspose E x y τ hx hy m n s r = 𝟙 _ := by
  apply doubleRank_hom_ext E x y n m r s
  · simp only [Category.assoc, doubleRankTranspose_map, doubleRankTranspose_map_assoc,
      hτ, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, doubleRankTranspose_first, doubleRankTranspose_second,
      Category.id_comp]
  · simp only [Category.assoc, doubleRankTranspose_second, doubleRankTranspose_first,
      Category.id_comp]

/-- Full independent rank stages are isomorphic with both indices and orders exchanged. -/
def doubleRankTransposeIso (hτ : τ ≫ τ = 𝟙 B) :
    doubleRankThickening E x y n m r s ≅ doubleRankThickening E x y m n s r where
  hom := doubleRankTranspose E x y τ hx hy n m r s
  inv := doubleRankTranspose E x y τ hx hy m n s r
  hom_inv_id := doubleRankTranspose_twice E x y τ hx hy n m r s hτ
  inv_hom_id := doubleRankTranspose_twice E x y τ hx hy m n s r hτ

end FLT.Mazur.RelativeOrderedTuples
