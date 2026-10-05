/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNonsplitNodeChart
public import FLT.Mazur.EllipticSmoothPointChange

/-!
# Smooth groups of arbitrary nonsplit nodal equations

A rational singular translation normalizes every nodal cubic over a perfect
field. Nonsplitting supplies irreducibility of the tangent quadratic, and
nonzero c₄ supplies separability. The normalized norm-one identification
then transports back to the original smooth point group.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] [PerfectField F] (W : WeierstrassCurve F)

/-- Normalize a nonsplit node with an irreducible, separable tangent quadratic. -/
theorem exists_nonsplitNode_variableChange (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hn : ¬ W.nodePoly.Splits) : ∃ C : VariableChange F,
    (C • W).a₃ = 0 ∧ (C • W).a₄ = 0 ∧ (C • W).a₆ = 0 ∧
      (C • W).b₂ ≠ 0 ∧ Irreducible (nodeTangentPolynomial (C • W)) := by
  obtain ⟨x, y, he, hs⟩ := exists_singular_of_discriminant_zero W hΔ
  let C : VariableChange F := ⟨1, x, 0, y⟩
  obtain ⟨h3, h4, h6⟩ := translated_singular_coefficients W he hs
  have hc' : (C • W).c₄ ≠ 0 := by simpa [C, variableChange_c₄] using hc
  have hb : (C • W).b₂ ≠ 0 := by
    intro hb
    apply hc'
    rw [normalized_c₄_eq_b₂_sq (C • W) h3 h4, hb, zero_pow (by decide : 2 ≠ 0)]
  have hn' : ¬ (C • W).nodePoly.Splits := by
    intro hs'
    apply hn
    simpa only [Polynomial.map_id] using
      (nodePoly_map_splits_smul_iff (RingHom.id F) W C).mp (by simpa using hs')
  exact ⟨C, h3, h4, h6, hb,
    nodeTangentPolynomial_irreducible_of_nonsplit (C • W) h3 h4 h6 hn'⟩

/-- A chosen rational singular translation of a nonsplit nodal equation. -/
noncomputable def nonsplitNodalChange (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hn : ¬ W.nodePoly.Splits) : VariableChange F :=
  (exists_nonsplitNode_variableChange W hΔ hc hn).choose

/-- The chosen translation satisfies all hypotheses of the normalized group theorem. -/
theorem nonsplitNodalChange_spec (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hn : ¬ W.nodePoly.Splits) : let V := nonsplitNodalChange W hΔ hc hn • W
    V.a₃ = 0 ∧ V.a₄ = 0 ∧ V.a₆ = 0 ∧ V.b₂ ≠ 0 ∧
      Irreducible (nodeTangentPolynomial V) :=
  (exists_nonsplitNode_variableChange W hΔ hc hn).choose_spec

variable [DecidableEq F]

/-- The actual smooth group of a nonsplit node is the norm-one group of its tangent field. -/
noncomputable def nonsplitNodalNormOneAddEquiv (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hn : ¬ W.nodePoly.Splits) :
    let V := nonsplitNodalChange W hΔ hc hn • W
    letI : Fact (Irreducible (nodeTangentPolynomial V)) :=
      ⟨(nonsplitNodalChange_spec W hΔ hc hn).2.2.2.2⟩
    W.toAffine.Point ≃+ Additive (nodeTangentNormOne V) := by
  classical
  let C := nonsplitNodalChange W hΔ hc hn
  obtain ⟨h3, h4, h6, hb, hi⟩ := nonsplitNodalChange_spec W hΔ hc hn
  letI : Fact (Irreducible (nodeTangentPolynomial (C • W))) := ⟨hi⟩
  exact (smoothPointChangeEquiv W C).symm.trans
    (nonsplitNodeNormOneAddEquiv (C • W) h3 h4 h6 hb)

omit [DecidableEq F] in
/-- Over a finite field, every nonsplit nodal cubic has |F|+1 smooth points. -/
theorem nonsplitNodalPoint_card [Fintype F] (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hn : ¬ W.nodePoly.Splits) : Nat.card W.toAffine.Point = Fintype.card F + 1 := by
  classical
  obtain ⟨C, h3, h4, h6, _, hi⟩ := exists_nonsplitNode_variableChange W hΔ hc hn
  let : Fact (Irreducible (nodeTangentPolynomial (C • W))) := ⟨hi⟩
  rw [← Nat.card_congr (smoothPointChangeEquiv W C).toEquiv]
  exact nonsplitNodePoint_card (C • W) h3 h4 h6

end FLT.Mazur
