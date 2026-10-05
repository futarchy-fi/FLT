/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNonsplitNormOneHom
public import FLT.Mazur.NodeTangentSlopeDescent

/-!
# The norm-one group of a normalized nonsplit node

Every nonidentity norm-one parameter descends to a ground-field slope.
The slope chart then supplies a smooth point, proving surjectivity of the
actual group homomorphism and identifying the full smooth point group.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]

local notation "L" => AdjoinRoot (nodeTangentPolynomial W)

/-- Every ground-field slope gives a smooth point on a normalized nonsplit node. -/
theorem nonsplitNode_nonsingular_slope
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (t : F) :
    W.toAffine.Nonsingular (t ^ 2 + W.a₁ * t - W.a₂)
      (t * (t ^ 2 + W.a₁ * t - W.a₂)) := by
  have he : W.toAffine.Equation (t ^ 2 + W.a₁ * t - W.a₂)
      (t * (t ^ 2 + W.a₁ * t - W.a₂)) := by
    rw [Affine.equation_iff']
    simp only [h3, h4, h6, zero_mul, add_zero]
    ring
  exact (normalized_nonsingular_iff W h3 h4 h6 he).mpr
    (fun h => nonsplit_tangent_value_ne_zero W t h.1)

/-- Every scalar of conjugation norm one is the tangent parameter of a smooth point. -/
theorem nodeTangentPointParameter_surjective_norm_one
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hb : W.b₂ ≠ 0)
    {u : L} (hn : nodeTangentConjugation W u * u = 1) :
    ∃ P : W.toAffine.Point, nodeTangentPointParameter W P = u := by
  by_cases hu : u = 1
  · exact ⟨0, hu.symm⟩
  · obtain ⟨t, ht⟩ := exists_nodeTangent_slope W hb hu hn
    let x := t ^ 2 + W.a₁ * t - W.a₂
    have hx : algebraMap F L x ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap F L).injective).mpr (nonsplit_tangent_value_ne_zero W t)
    have hp := nonsplitNode_nonsingular_slope W h3 h4 h6 t
    refine ⟨.some x (t * x) hp, ?_⟩
    have hd := (nodeTangentPoint_factors_ne_zero W h3 h4 h6 hp).2
    have ht' := (eq_div_iff (sub_ne_zero.mpr (Ne.symm hu))).mp ht
    change (algebraMap F L (t * x) - AdjoinRoot.root (nodeTangentPolynomial W) *
        algebraMap F L x) / (algebraMap F L (t * x) +
          (algebraMap F L W.a₁ + AdjoinRoot.root (nodeTangentPolynomial W)) *
            algebraMap F L x) = u
    apply (div_eq_iff hd).mpr
    rw [map_mul]
    linear_combination algebraMap F L x * ht'

variable [DecidableEq F] [DecidableEq (AdjoinRoot (nodeTangentPolynomial W))]

/-- The actual norm-one homomorphism is surjective. -/
theorem nonsplitNodeNormOneHom_surjective
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hb : W.b₂ ≠ 0) :
    Function.Surjective (nonsplitNodeNormOneHom W h3 h4 h6) := by
  intro u
  obtain ⟨P, hP⟩ := nodeTangentPointParameter_surjective_norm_one W h3 h4 h6 hb
    ((mem_nodeTangentNormOne_iff W _).mp (Additive.toMul u).property)
  refine ⟨P, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change ((Additive.toMul (nodeTangentPointHom W h3 h4 h6 P) : Lˣ) : L) = _
  rw [nodeTangentPointHom_val]
  exact hP

/-- The smooth point group of a normalized nonsplit node is its tangent norm-one group. -/
noncomputable def nonsplitNodeNormOneAddEquiv
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hb : W.b₂ ≠ 0) :
    W.toAffine.Point ≃+ Additive (nodeTangentNormOne W) :=
  AddEquiv.ofBijective (nonsplitNodeNormOneHom W h3 h4 h6)
    ⟨nonsplitNodeNormOneHom_injective W h3 h4 h6 hb,
      nonsplitNodeNormOneHom_surjective W h3 h4 h6 hb⟩

end FLT.Mazur
