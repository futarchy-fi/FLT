/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedVariableRetainedIntersection

/-!
# Reflection of all original retained intersections

Full corrected retained charts retain their exact puncture preimages.
The target classification and unchanged original adjacent squares therefore
reflect every retained/retained equality into the original global stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
/-- Only the earlier node needs its outgoing preimage to reflect a retained intersection. -/
theorem revisedRetained_preimage_transport (S : Type*) [CommRing S] (s t : S) (k : ℕ)
    (C : Fin k → Bool → (PolygonSmoothing.chart S s ⟶ PolygonSmoothing.chart S t))
    (hp : ∀ idx b, idx.val + 1 < k → ∀ x,
      C idx b x ∈ Set.range (leftBranchOpen S t) → x ∈ Set.range (leftBranchOpen S s))
    (idx other : Fin k) (b e : Bool) (x y : PolygonSmoothing.chart S s)
    (h : (idx = other ∧ b = e) ∨
      (idx.val + 1 = other.val ∧ b = e ∧ C idx b x ∈ Set.range (leftBranchOpen S t)) ∨
      (other.val + 1 = idx.val ∧ b = e ∧ C other e y ∈ Set.range (leftBranchOpen S t))) :
    (idx = other ∧ b = e) ∨
      (idx.val + 1 = other.val ∧ b = e ∧ x ∈ Set.range (leftBranchOpen S s)) ∨
      (other.val + 1 = idx.val ∧ b = e ∧ y ∈ Set.range (leftBranchOpen S s)) := by
  rcases h with hs | ⟨hi, hb, hx⟩ | ⟨hi, hb, hy⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl ⟨hi, hb, hp idx b (by omega) x hx⟩)
  · exact Or.inr (Or.inr ⟨hi, hb, hp other e (by omega) y hy⟩)

/-- Classifying a family after composition needs only its morphism equations. -/
theorem revisedRetained_composite_intersection {X Y Z : Scheme} (k : ℕ)
    (C : Fin k → Bool → (X ⟶ Y)) (O : Bool → (Y ⟶ Y))
    (r : Fin k → Bool → (Y ⟶ Z)) (G : Fin k → Bool → (X ⟶ Z))
    (hG : ∀ i b, G i b = C i b ≫ O b ≫ r i b) (U : Set Y)
    (hc : ∀ i d b e x y, r i b (O b x) = r d e (O e y) →
      (i = d ∧ b = e) ∨
        (i.val + 1 = d.val ∧ b = e ∧ x ∈ U) ∨
        (d.val + 1 = i.val ∧ b = e ∧ y ∈ U))
    (i d : Fin k) (b e : Bool) (x y : X) (h : G i b x = G d e y) :
    (i = d ∧ b = e) ∨
      (i.val + 1 = d.val ∧ b = e ∧ C i b x ∈ U) ∨
      (d.val + 1 = i.val ∧ b = e ∧ C d e y ∈ U) := by
  apply hc i d b e (C i b x) (C d e y)
  rw [hG i b, hG d e] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
