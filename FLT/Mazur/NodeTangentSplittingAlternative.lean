/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentCoefficientNaturality
public import FLT.Mazur.EllipticNodeTangent
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The two tangent cases of a normalized nodal cubic

A normalized special fiber either has split node polynomial, or its tangent
quadratic is irreducible. Thus the quadratic DVR construction applies whenever
the split normalization construction does not.
-/

@[expose] public section
open WeierstrassCurve IsLocalRing Polynomial
namespace FLT.Mazur

/-- A normalized field cubic has either split node polynomial or irreducible tangent. -/
theorem normalized_node_split_or_irreducible {F : Type*} [Field F]
    (W : WeierstrassCurve F) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    W.nodePoly.Splits ∨ Irreducible (nodeTangentPolynomial W) := by
  classical
  by_cases hs : W.nodePoly.Splits
  · exact Or.inl hs
  right
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_eq_of_degree_eq_some (nodeTangentPolynomial_degree W)]
    decide
  intro s hr
  apply hs
  rw [normalized_nodePoly W h3 h4 h6]
  apply (Splits.C _).mul
  have he : s ^ 2 + W.a₁ * s + -W.a₂ = 0 := by
    simpa [IsRoot, nodeTangentPolynomial, sub_eq_add_neg] using hr
  have ht := (splits_quadratic_iff_exists_root (a := (1 : F))
    (b := W.a₁) (c := -W.a₂) one_ne_zero).mpr ⟨s, by simpa using he⟩
  simpa [sub_eq_add_neg] using ht

/-- The same dichotomy holds for the actual residue tangent of an integral equation. -/
theorem residue_node_split_or_irreducible {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) (h3 : W.a₃ ∈ maximalIdeal R)
    (h4 : W.a₄ ∈ maximalIdeal R) (h6 : W.a₆ ∈ maximalIdeal R) :
    (W.nodePoly.map (residue R)).Splits ∨
      Irreducible ((nodeTangentPolynomial W).map (residue R)) := by
  have h := normalized_node_split_or_irreducible (W.map (residue R))
    ((residue_eq_zero_iff _).mpr h3) ((residue_eq_zero_iff _).mpr h4)
    ((residue_eq_zero_iff _).mpr h6)
  simpa only [map_nodePoly, nodeTangentPolynomial_map_coefficients] using h

end FLT.Mazur
