/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankTransitions
public import FLT.Mazur.RelativeDoubleRankTestDetection
public import FLT.Mazur.RelativeDoubleRankTransposition

/-!
# Naturality of independent rank order transitions

Order transitions commute with arbitrary coefficient tests and endpoint
transposition on the entire schemes. Consequently equations transported by
either operation are compatible with every later ideal-power restriction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B T : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (n m : ℕ)

/-- Changing coefficients commutes with increasing the two independent full orders. -/
@[reassoc]
theorem doubleRankTransition_test (v : T ⟶ B) {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankTransition E (v ≫ x) (v ≫ y) n m hr hs ≫
        doubleRankTestMap E x y v n m r' s' =
      doubleRankTestMap E x y v n m r s ≫ doubleRankTransition E x y n m hr hs := by
  apply (cancel_mono (doubleRankMap E x y n m r' s')).mp
  simp only [Category.assoc, doubleRankTestMap_projection,
    doubleRankTransition_map_assoc, doubleRankTransition_map]

/-- Transposition exchanges both order increases as well as both ranks. -/
@[reassoc]
theorem doubleRankTransition_transpose (τ : B ⟶ B)
    (hx : τ ≫ x = y) (hy : τ ≫ y = x) {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankTransition E x y n m hr hs ≫ doubleRankTranspose E x y τ hx hy n m r' s' =
      doubleRankTranspose E x y τ hx hy n m r s ≫ doubleRankTransition E x y m n hs hr := by
  apply (cancel_mono (doubleRankMap E x y m n s' r')).mp
  simp only [Category.assoc, doubleRankTranspose_map,
    doubleRankTransition_map_assoc, doubleRankTransition_map]

/-- Restrict a full higher-order equation along the constructed transition. -/
theorem doubleRankTransition_section_eq {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') (a b : Γ(B, ⊤))
    (h : (doubleRankMap E x y n m r' s').appTop a =
      (doubleRankMap E x y n m r' s').appTop b) :
    (doubleRankMap E x y n m r s).appTop a =
      (doubleRankMap E x y n m r s).appTop b := by
  have h' := congrArg (doubleRankTransition E x y n m hr hs).appTop h
  change ((doubleRankTransition E x y n m hr hs ≫
    doubleRankMap E x y n m r' s').appTop a) =
      ((doubleRankTransition E x y n m hr hs ≫
        doubleRankMap E x y n m r' s').appTop b) at h'
  simpa only [doubleRankTransition_map] using h'

end FLT.Mazur.RelativeOrderedTuples
