/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentExtension
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Nonsplit reduction supplies the irreducible tangent polynomial

For a node normalized to the origin, nonsplitting of the existing node
polynomial forces the monic tangent quadratic to be irreducible. Thus the
quadratic DVR construction applies directly to nonsplit special fibers.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve Polynomial IsLocalRing

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- A rational root of the tangent quadratic splits it. -/
theorem nodeTangentPolynomial_splits_of_root {s : F}
    (hs : (nodeTangentPolynomial W).IsRoot s) : (nodeTangentPolynomial W).Splits := by
  have he : s ^ 2 + W.a₁ * s - W.a₂ = 0 := by
    simpa [Polynomial.IsRoot, nodeTangentPolynomial] using hs
  have hp : nodeTangentPolynomial W = C 1 * X ^ 2 + C W.a₁ * X + C (-W.a₂) := by
    simp [nodeTangentPolynomial, sub_eq_add_neg]
  rw [hp, splits_quadratic_iff_exists_root one_ne_zero]
  exact ⟨s, by simpa [sub_eq_add_neg] using he⟩

/-- A normalized nonsplit node has irreducible tangent quadratic. -/
theorem nodeTangentPolynomial_irreducible_of_nonsplit
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (hn : ¬ W.nodePoly.Splits) : Irreducible (nodeTangentPolynomial W) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_eq_of_degree_eq_some (nodeTangentPolynomial_degree W)]
    decide
  · intro s hs
    apply hn
    rw [normalized_nodePoly W h3 h4 h6]
    exact (Splits.C _).mul (nodeTangentPolynomial_splits_of_root W hs)

/-- The tangent polynomial commutes with every coefficient map. -/
theorem nodeTangentPolynomial_map {S : Type*} [CommRing S] (f : F →+* S) :
    nodeTangentPolynomial (W.map f) = (nodeTangentPolynomial W).map f := by
  simp [nodeTangentPolynomial]

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A normalized nonsplit special fiber admits a quadratic integral tangent extension
preserving its uniformizer. -/
theorem exists_nonsplit_node_tangent_extension (E : WeierstrassCurve R)
    (h3 : E.a₃ ∈ maximalIdeal R) (h4 : E.a₄ ∈ maximalIdeal R)
    (h6 : E.a₆ ∈ maximalIdeal R) (hc : IsUnit E.c₄)
    (hn : ¬ (E.map (residue R)).nodePoly.Splits)
    (π : R) (hπ : maximalIdeal R = Ideal.span {π}) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S) (_ : Module.Finite R S) (_ : IsLocalHom (algebraMap R S)),
      Module.finrank R S = 2 ∧ maximalIdeal S = Ideal.span {algebraMap R S π} ∧
      ∃ s : S, s ^ 2 + algebraMap R S E.a₁ * s - algebraMap R S E.a₂ = 0 ∧
        IsUnit (algebraMap R S E.a₁ + 2 * s) := by
  have he3 : (E.map (residue R)).a₃ = 0 := (residue_eq_zero_iff _).mpr h3
  have he4 : (E.map (residue R)).a₄ = 0 := (residue_eq_zero_iff _).mpr h4
  have he6 : (E.map (residue R)).a₆ = 0 := (residue_eq_zero_iff _).mpr h6
  have hb : IsUnit E.b₂ := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hz
    have he := normalized_c₄_eq_b₂_sq (E.map (residue R)) he3 he4
    rw [map_c₄, map_b₂, hz, zero_pow (by decide : 2 ≠ 0)] at he
    exact (residue_ne_zero_iff_isUnit _).mpr hc he
  apply exists_node_tangent_extension E _ hb π hπ
  have hi := nodeTangentPolynomial_irreducible_of_nonsplit (E.map (residue R))
    he3 he4 he6 hn
  simpa [nodeTangentPolynomial] using hi

end FLT.Mazur
