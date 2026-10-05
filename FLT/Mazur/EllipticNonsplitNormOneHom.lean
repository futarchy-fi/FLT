/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTangentParameterHom

/-!
# Embedding the nonsplit smooth group into the norm-one subgroup

The canonical tangent conjugation defines a norm-one subgroup of the
quadratic field's units. The actual tangent-ratio homomorphism lands in this
subgroup and is injective. Surjectivity remains a separate descent step.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]

local notation "L" => AdjoinRoot (nodeTangentPolynomial W)

/-- The conjugation norm on units of the quadratic tangent field. -/
noncomputable def nodeTangentConjugationNorm : Lˣ →* Lˣ :=
  (Units.map (nodeTangentConjugation W).toMonoidHom) * MonoidHom.id Lˣ

/-- The norm-one subgroup for canonical tangent conjugation. -/
noncomputable def nodeTangentNormOne : Subgroup Lˣ := (nodeTangentConjugationNorm W).ker

/-- Membership in the norm-one subgroup is the scalar conjugation identity. -/
theorem mem_nodeTangentNormOne_iff (u : Lˣ) : u ∈ nodeTangentNormOne W ↔
    nodeTangentConjugation W (u : L) * (u : L) = 1 := by
  change nodeTangentConjugationNorm W u = 1 ↔ _
  exact Units.ext_iff

variable [DecidableEq F] [DecidableEq (AdjoinRoot (nodeTangentPolynomial W))]

/-- The actual smooth-point homomorphism with codomain restricted to norm-one units. -/
noncomputable def nonsplitNodeNormOneHom
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    W.toAffine.Point →+ Additive (nodeTangentNormOne W) where
  toFun P := Additive.ofMul ⟨Additive.toMul (nodeTangentPointHom W h3 h4 h6 P), by
    rw [mem_nodeTangentNormOne_iff, nodeTangentPointHom_val]
    exact nodeTangentPointParameter_norm_one W h3 h4 h6 P⟩
  map_zero' := Subtype.ext (map_zero (nodeTangentPointHom W h3 h4 h6))
  map_add' P Q := Subtype.ext (map_add (nodeTangentPointHom W h3 h4 h6) P Q)

/-- The norm-one homomorphism is injective for a separable nonsplit node. -/
theorem nonsplitNodeNormOneHom_injective
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hb : W.b₂ ≠ 0) :
    Function.Injective (nonsplitNodeNormOneHom W h3 h4 h6) := by
  intro P Q he
  apply nodeTangentPointParameter_injective W h3 h4 h6 hb
  have hu := congrArg (fun z : Additive (nodeTangentNormOne W) =>
    (((Additive.toMul z : nodeTangentNormOne W) : Lˣ) : L)) he
  change ((Additive.toMul (nodeTangentPointHom W h3 h4 h6 P) : Lˣ) : L) =
    ((Additive.toMul (nodeTangentPointHom W h3 h4 h6 Q) : Lˣ) : L) at hu
  simpa only [nodeTangentPointHom_val] using hu

end FLT.Mazur
