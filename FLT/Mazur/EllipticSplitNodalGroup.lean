/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitNodeGroup
public import FLT.Mazur.EllipticNodeTangent
public import FLT.Mazur.EllipticSmoothPointChange

/-!
# Smooth groups of arbitrary split nodal equations

Over a perfect field, a zero discriminant, nonzero c₄, and a split node
polynomial identify the actual smooth point group with the field's units.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] [PerfectField F] (W : WeierstrassCurve F)

/-- A split nodal equation admits a normalized split-node model. -/
theorem exists_splitNodeCurve_variableChange (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hsplit : W.nodePoly.Splits) :
    ∃ (C : VariableChange F) (a : F), a ≠ 0 ∧ C • W = splitNodeCurve a := by
  obtain ⟨x, y, he, hn⟩ := exists_singular_of_discriminant_zero W hΔ
  let T : VariableChange F := ⟨1, x, 0, y⟩
  obtain ⟨h3, h4, h6⟩ := translated_singular_coefficients W he hn
  have hc' : (T • W).c₄ ≠ 0 := by simpa [T, variableChange_c₄] using hc
  have hs' : (T • W).nodePoly.Splits := by
    simpa only [Polynomial.map_id] using
      (nodePoly_map_splits_smul_iff (RingHom.id F) W T).mpr (by simpa using hsplit)
  obtain ⟨s, h1, h2, h3, h4, h6⟩ :=
    exists_normalized_node_shear (T • W) h3 h4 h6 hc' hs'
  refine ⟨VariableChange.mk 1 0 s 0 * T, (VariableChange.mk 1 0 s 0 • T • W).a₁, h1, ?_⟩
  rw [mul_smul]
  exact WeierstrassCurve.ext rfl h2 h3 h4 h6

variable [DecidableEq F]

/-- The smooth point group of a split nodal cubic is the units of its perfect field. -/
noncomputable def splitNodalPointAddEquiv (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hsplit : W.nodePoly.Splits) : W.toAffine.Point ≃+ Additive Fˣ := by
  let C := (exists_splitNodeCurve_variableChange W hΔ hc hsplit).choose
  let a := (exists_splitNodeCurve_variableChange W hΔ hc hsplit).choose_spec.choose
  have ha : a ≠ 0 := (exists_splitNodeCurve_variableChange W hΔ hc hsplit).choose_spec.choose_spec.1
  have hC : C • W = splitNodeCurve a :=
    (exists_splitNodeCurve_variableChange W hΔ hc hsplit).choose_spec.choose_spec.2
  exact (smoothPointChangeEquiv W C).symm.trans
    ((Affine.Point.equivOfEq hC).trans (splitNodeParameterAddEquiv ha))

omit [DecidableEq F] in
/-- Over a finite field, the smooth split-node group has one fewer point than the field. -/
theorem splitNodalPoint_card [Fintype F] (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (hsplit : W.nodePoly.Splits) : Nat.card W.toAffine.Point = Fintype.card F - 1 := by
  classical
  rw [Nat.card_congr (splitNodalPointAddEquiv W hΔ hc hsplit).toEquiv]
  exact (Nat.card_congr (Additive.toMul : Additive Fˣ ≃ Fˣ)).trans
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units])

end FLT.Mazur
